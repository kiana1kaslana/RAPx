# RAPx opt：从模式提示到有证据的优化候选

调研日期：2026-10-20。基线：上游 a4027f0（v0.7.60 工作树）。
本次工作只涉及 opt、对应回归和研究/基准材料，不改 verify 证明引擎。

## 结论与建议选题

建议主线是：**基于语义证据和实际代价的 Rust 性能机会识别**。
首先解决 checked → unchecked 的正确性，再研究循环中的重复复制/分配。
AI 生成代码适合作为有明确来源的评测对象，而不是通过源码猜测“是否由 AI 编写”。
不要把“可以去掉检查”“编译后仍有检查”和“去掉后有可测收益”混为一谈。

本次实现是这条 pipeline 的第一步，不是完整的路径敏感证明器，也没有证明所有
opt 告警都正确。尤其 bounds 的循环规则仍然是候选发现器。

## 当前 opt 在做什么

入口位于 rapx/src/check/opt/mod.rs；CLI 的 opt 固定调用 Opt::new(tcx, 1)。
先为函数建立基于 MIR 的 DataflowGraph，再运行六组检查。部分规则依赖 HIR 扫描循环。
DataflowGraph 用 Local 聚合操作，一个 local 的多次赋值共享节点，span 会被后一次操作覆盖。
因此节点之间存在路径不等于“这个调用的这个参数满足某个前置条件”。

| 组别 | 基线规则 | 主要局限 |
|---|---|---|
| Bounds | 长度相关索引、循环 push、extend_from_slice | 祖先相交不是数值证明；需要区分 i 与 i+1、容器变更和守卫真假；编译器可能已消除检查 |
| Encoding | 数组/Vec 转 UTF-8、String push、lowercase | 常量 u8 不等于合法 UTF-8；Unicode lowercase 不等于 ASCII lowercase；char 编码不等于多余校验 |
| Suboptimal | Vec 首部增删、slice contains、集合选择 | 需要操作频率、容器规模和顺序语义；不能见 contains 就建议 HashSet |
| Initialization | Vec 初始化、本地集合初始化 | 未证明所有读取前都被写入；跳过初始化可能破坏安全条件 |
| Reallocation | Vec/Hash 扩容、flatten collect | 需要同一容器身份、容量/长度关系、reserve 成功路径和逃逸信息 |
| Cloning | 克隆后使用 | 只看第一个使用点；非 &mut 参数也可能按值取得所有权；需要全用途/生命周期/副作用证据 |

level=2 才运行的规则在当前 CLI 默认路径中不启用。不能把它们全部算作默认检测覆盖。
全局 OnceCell/Mutex、无稳定 rule ID、报告缺乏结构化证据，以及没有 release 成本过滤，
都是后续工程问题。先分规则迁移，避免同时改动底层公共分析和全部 checker。

## 本次已复现和处理的问题

1. 7 个编码反例在基线上全部误报，包括 ÉCOLE.to_lowercase()、
   任意 str 参数、push(0xff)、push 后再改写为 0xff、数组非法常量写入、
   混合常量和未知字节，以及有实际替换字符语义的 from_utf8_lossy。
   新编码规则不再对这些反例给出优化建议。
2. if i < len || force 和 if !(i < len) 都曾被报告为已满足上界，
   并建议 unsafe。现在只识别直接为真的小于比较，不再从否定/析取中抽取子表达式。
   同时修复原来的遍历遗漏条件根节点问题，恢复直接 while 条件候选；
   原 bounds_len fixture 因此从两个 Vec 索引站点增加到三个站点。
3. 不再输出没有索引站点的空 bounds 报告。bounds 文案明确是候选，
   移除“直接改用 unsafe”的建议。该变化不代表已经实现 bounds 完整证明。
4. 原有未合入的 feat/opt-string-add 分支认为 String + &str 每次复制整个左操作数。
   这个假设与标准库语义不符，本次没有 cherry-pick 该分支。
   新增的是循环内 s = s.clone() + suffix：标准 String 类型、真实 Clone 方法、
   同一局部变量写回、变量在循环外定义；排除普通 +、+=、push_str、
   非 String、不同源变量、循环内新建/clear/重置和非循环调用。
   它是成本候选，不提供自动替换，也不假定每个循环一定增长或执行多次。

## 已实现的编码证据层

新增 evidence.rs，编码规则先定位具体 MIR 调用，再查询该调用实际输入的事实：

- Unknown：无法证明；不产生编码建议。
- Ascii：整个输入仅包含 ASCII；也满足 UTF-8。
- Utf8：整个输入合法 UTF-8；不能推出 ASCII。

证据来源包括经常量求值读取的完整字节、只读局部值复制、数组整体构造、
已知 str/String 字节转换和保留全部字节的 slice.to_vec。
读取编译器分配时检查范围、初始化和 provenance，不解析 Debug 字符串。
任意字节切片/索引不能继承 Utf8；ASCII 的任意字节子集才仍是 ASCII。
未知调用、重复定义、可变/原始指针借用、投影写入、内联汇编和协程恢复等
未建模情况保守放弃。只在发现编码候选后构造分析，标准 API 身份按编译会话缓存。

当前版本有意不分析可变缓冲区的逐次写入。原 encoding_check 中两个动态构造样例
暂时返回未知，测试已显式记录这项覆盖率取舍；并非宣称它们没有优化空间。
新增 encoding_proven 保留 8 个可证明候选，其中有合法非 ASCII 的 UTF-8，
以及“一个未知候选不能抹掉另一个已证候选”的混合用例。
编码反例还覆盖局部别名、分支重新赋值、未知函数修改和截断多字节序列。

报告保留 Result/Cow 返回契约提醒，优先复用原 str/字面量；
证明 UTF-8 有效也不意味着可以无条件把 Result API 改成直接返回值。

## 推荐的完整 pipeline

~~~text
HIR + DefId 候选发现
  → typed MIR 调用/索引位置与对象身份
  → 切片得到必要依赖
  → 路径、数值、别名、写入覆盖等前置条件
  → 语义证据 / Unknown（停止）
  → release 代码中残余检查与复制/分配代价
  → 差分正确性测试 + 成本基准
  → 带证据、限制和预期适用范围的报告
~~~

下一阶段应引入 Candidate(rule_id, owner, MIR Location, span, object_version)。
对象和版本需要与调用位置绑定，不能只使用 Local 或 source span。
数值/内存事实在 CFG 汇合点取所有可达前驱共同成立的事实；异常路径、
循环回边和无法建模的调用不能当作成功证明。超时/不支持返回 Unknown。

各规则的证明义务不同：

| 规则 | 必须满足的语义条件 | 代价条件 |
|---|---|---|
| UTF-8 检查 | 该次输入的完整字节有效，所有写入/切片均保留性质 | 优化后验证仍存在且输入规模足够 |
| ASCII lowercase | 当前输入的所有字符都是 ASCII | Unicode 路径相较 ASCII 路径确有测得收益 |
| 索引 unchecked | 当前索引在当前对象长度内；守卫支配访问；中间无相关失效 | release 中仍有边界检查 |
| 跳过初始化 | 所有读取/析构/异常路径所需区域均已初始化，元素类型约束成立 | 初始化确实冗余且未被编译器删除 |
| clone → borrow | 全部用途仅借用、生命周期可满足、原对象不冲突、不改变可观察 Clone 行为 | 存在真实复制或分配成本 |
| reserve | 同一容器、成功路径、容量需求和循环次数可约束 | 分配次数/峰值内存有改善 |

对 bounds，优先完成不可变 slice + 直接守卫，再扩展 Vec 长度版本和循环归纳变量。
安全迭代器重写优先于 unchecked；证明失败应留下可审计原因，不能升级为确定告警。
收益验证先做离线评测，避免每次静态扫描都运行被分析的用户程序。

## 新 pattern 的实际优化空间

tools/opt/bench_string_accumulator.rs 比较 clone+add、move+add、push_str。
编译为 release 优化级别，固定 CPU 0，每组 30 次，轮换顺序，预热，使用 black_box，
每次均验证输出。原始数据在 tools/opt/results/string-accumulator-2026-10-20.csv。

环境：WSL2 Linux 5.15.167.4、AMD Ryzen 9 7940HX、
rustc 1.101.0-nightly (d080e7dff 2026-09-27)。每次追加 32 字节。

| 追加次数 | clone + add 中位 μs | move + add 中位 μs | push_str 中位 μs |
|---|---:|---:|---:|
| 100 | 7.284 | 0.790 | 0.395 |
| 1,000 | 345.980 | 6.528 | 2.626 |
| 10,000 | 79,174.796 | 108.902 | 23.566 |

这些是一个合成微基准的描述性数据，不是总体提速比例或统计显著性声明。
它支持“反复复制累积前缀值得识别”，不支持“所有字符串 + 都是二次复杂度”。
普通 + 与 push_str 在本机也有常数差异；两者都没有显式全前缀 clone。
独立语义测试覆盖空输入、空片段、ASCII 和 Unicode。

本机 Clippy all + pedantic + nursery 对该 fixture 的普通 + 报 string_add_assign，
对整数 clone 报 clone_on_copy，但没有在两个目标函数上报冗余 String clone。
这只是版本和样例限定的覆盖差异，不是“Clippy 永远检测不到”的结论。
format_push_string、needless_collect、redundant_iter_cloned 等已有 lint
应作为基线，避免把重复实现包装成新研究贡献。

## AI 生成代码：可以做，但需要正确的研究设计

EffiBench 已研究生成代码效率；EffiBench-X 的六种语言不包含 Rust。
这支持做 Rust 专项评测的动机，但不能单凭语言空缺声称学术创新。
建议假设是：“语义证据约束的修复能降低不安全建议，同时找到编译器和
现有 lint 未覆盖、在真实输入规模下有收益的候选。”

建议先建立 30–50 个 Rust 小任务试验集，再按结果扩展：

1. 从有明确许可的真实 API 使用任务和人工最小反例出发，记录原始出处/commit。
   生成样本记录模型、版本、完整提示和采样配置；来源不明的社区代码不标作 AI。
2. 同题保存人工基线、未修复生成结果、lint 修复、RAPx 证据约束修复。
   正确性测试先于性能筛选，不能只保留容易优化的成功样本。
3. 覆盖输入大小、空值、Unicode、失败路径和对象突变；性能测试需有代表性工作量。
   对比 release rustc、固定 Clippy 版本、原 RAPx、新 RAPx，并做证据层消融。
4. 分别报告建议精确率、经人工核实的漏报、错误语义建议数、分析耗时、
   端到端时间、分配次数/峰值内存及置信区间。
   不用“告警越多越好”或平均加速比掩盖超时/退化。
5. 按仓库和 pattern 家族划分开发/测试集，保留 Unknown，不让同源变体跨集合泄漏。

2026 年的 Rethinking Code Performance Benchmarks for LLMs 强调：
性能测试本身不充分时，即使源码看起来优化了，也不一定测出有意义的改善。
因此本次提交只有手工构造的回归和微基准，尚未建立或评测真实 AI 生成代码数据集。

建议里程碑：先锁定编码反例与报告契约；再实现 slice/Vec 的版本化 bounds 证明；
然后迁移 clone/reserve；最后建立真实项目和有来源的 AI 样本评测。
新增 pattern 的优先级以“现有工具覆盖缺口 × 真实收益 × 可证明性”排序。

## 本次验证边界

- 当前 nightly 的 7 项 opt 集成回归通过。
- 字符串 fixture 的输出等价性测试通过；release 微基准每个样本也检查输出。
- 修改过的 Rust 文件通过 rustfmt；git diff --check 通过。
- 额外尝试 nightly-2026-09-01 的离线 cargo check：新增 opt 代码的接口已适配，
  但整个项目仍失败于未修改的 verify/vm/region.rs:24（RegionExt 不在作用域）。
  该文件与 a4027f0 完全相同；本次没有越过 opt 范围修改 verify。
  因此不能声称第二工具链或全部仓库测试通过。
- 尚未进行真实 AI 生成代码评测、真实项目总体收益统计或完整 bounds 安全证明。

## 参考资料

- [String 的 Add 实现语义](https://doc.rust-lang.org/std/string/struct.String.html#impl-Add%3C%26str%3E-for-String)：复用左侧缓冲区。
- [from_utf8_unchecked 安全前置条件](https://doc.rust-lang.org/std/str/fn.from_utf8_unchecked.html)：输入必须有效 UTF-8。
- [Rust str API](https://doc.rust-lang.org/std/primitive.str.html#method.to_ascii_lowercase)：ASCII 与 Unicode 大小写转换的区别。
- [Clippy lint 目录](https://rust-lang.github.io/rust-clippy/master/index.html)：检查已有模式和适用性。
- [EffiBench, NeurIPS 2024](https://proceedings.neurips.cc/paper_files/paper/2024/hash/15807b6e09d691fe5e96cdecde6d7b80-Abstract-Datasets_and_Benchmarks_Track.html)。
- [EffiBench-X, 2025](https://arxiv.org/abs/2505.13004)。
- [Rethinking Code Performance Benchmarks for LLMs, 2026](https://arxiv.org/abs/2607.07619)。
