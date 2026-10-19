# 一般真实边界、单轨道与完整物理轮廓：独立 AI 语义核查

核查日期：2026-10-19（北京时间）。核查代理 `/root/boundary_method_record`；只读 Lean 源码、既有依赖 definitions 与已有构建日志，没有编辑证明或重新构建。AI 审阅不是人类专家认证，不能替代标准 Lean Kernel。

## 观察快照与验收范围

本次覆盖八个实际正式路径中的模块：

| 模块 | 已核对作用域 |
|---|---|
| GridRegionConnectivity | actual occupied 四邻路径到实际单位格并集 preconnected/非空 connected |
| OrthogonalBoundaryConnectivity | 仅 ColumnConvex+FourConnected 下，所有 actual half-edge 的真实端点 Touch 连通 |
| OrthogonalBoundaryCycle | 从离散条件构造单 successor cycle、真实全边/顶点枚举 |
| OrthogonalBoundaryPolygon | 全真实实线段 polygon、真实点无重复、非相邻边无交 |
| OrthogonalBoundaryCurve | 连续分段仿射闭 trace、半开周期单射、全线段像 |
| OrthogonalContourLength | genuine Euclidean eVariationOn，全部有限单调分割的弧长 |
| OrthogonalPhysicalContour | 完整 actual unitRegion frontier 的简单连续闭曲线、真实最小矩形周长 |
| ProtectedGeometricGood | Shape 到既有 GeometricGood，以及真实 modified/stopped 事件轨迹严格退出前 Good |

各源快照 SHA256、声明名及计数存于[机读独立证据](orthogonal-boundary-independent-evidence.json)。当前是观察快照，不冒充之后源码修改的审计。已有首次 Connectivity、Cycle、Polygon、Curve 与 PhysicalContour 构建日志均成功可见；后者包括 ContourLength。只保留 batteries 已知本地修改 warning，当前新模块成功日志未见 Lean 源码 warning。ProtectedGeometricGood 亦已由根代理报告实际模块构建退出0、无新源码warning，当前冻结八源待专项与统一审计。根代理先前报告 Connectivity 草稿 standalone trust0 成功，旧草稿 tactic lint 不等于正式冻结版失败。

**最终冻结专项及全局统一验收现已逐项独立核对成功。** 新增8模块92条定理/114个def、abbrev、theorem命名声明全部有标准trust0公理输出；统一153分析源/2076分析定理，结合8核心源/125定理及1模型，共161正式源、2201辅助定理、2202全局输出。旧153源/1984分析定理作为历史基线保留，不重复计数。全部当前源指纹、144个旧分析证明模块不变及8核心源均已核对；只3标准公理。

## 数学与语义结论

对实际代码中的精确结论，未发现条件偷换、目标内置假设或逻辑作用域漏洞。核心输入是有限格点集合的实际截面凸性、actual 四邻路径及局部 NoCheckerboard；原单轨道、曲线简单性、完整 frontier 或概率结论没有存成输入。

### 1. 从集合路径到边界路径

`GridRegionConnectivity` 以实际相邻 unitCell 的真实公共中点证交非空，再提升原 FourConnected 的 occupied 路径，证明 unitRegion preconnected，非空时 connected。它不将区域 connected 当作 frontier connected。

`OrthogonalBoundaryConnectivity.Step` 显式要求两端 actual half-edge 属于 `boundary S`，再要求 actual source/target 的端点接触。`Path` 是 Step 的 reflexive-transitive closure；最终 `boundary_path_between` 显式接受 he/hf。它仅要求 ColumnConvex 与实际 FourConnected，没有把边界连通当输入，也没有 ±1 列高差限制。

`north_occupied_le` 从列凸和 north-empty 推出该列真实顶端。`north_adjacent_path` 用实际四邻路径跨竖 cut 找共同占据高度，再由列凸填满较高列的竖桥，另一列顶端排除桥外邻格。任意高度差都成立：较高右列用 west 桥 z=u.y+1..v.y，`source(Nu)=target(W首)`、`source(W末)=target(Nv)`；较高左列用 east 桥并反转，`target(Nv)=source(E首)`、`target(E末)=source(Nu)`。高度相等直接共享端点。`north_path_of_le` 通过实际连通投影区间逐列归纳，所有中间列 north 端点均由有限极值引理实际取得。

### 2. 真实反射与两条脊柱

`mirror false true` 是 actual image (x,y)↦(x,-y)。`flipDirection` 交换 N/S、保持 E/W；代码正确计入反射改变定向，实际证明 `source(flip e)=R(target e)`、`target(flip e)=R(source e)`，并运输 boundary membership 和四种 Touch 端点等式。`south_path` 在镜像集合使用 north_path 后，再实际反射路径回 S，凭 mirror_mirror/flip_flip 消去二次反射；没有假定反射保 source 定向。

`side_path_to_spine` 对任意 E/W 暴露边分两种真实情形：若其高度至本列北端的邻列格一直空，沿完整侧边向北；若上方某邻列格占据，则邻列列凸加当前外邻空，排除当前及更低的全部邻列格，故沿本列完整侧边向南到真实 south 端点。两分支的 owner 均由本列列凸填充。

`spines_connected` 仅需列凸和非空，取有限 x 投影真实最小列，整列 west 外邻为空，从该列 south 边经真实 west 链连接至 north 边。`boundary_path_between` 从 he 的 owner 得 S.Nonempty；穷尽实际方向0/1/2/3，将全部边接入两脊柱及固定北端，再反转与传递连接任意 e/f。空集无 he，结论正确真空成立。

### 3. Region 只存局部离散条件，单 cycle 和枚举由证明产生

`OrthogonalBoundaryCycle.Region` 的确仅为 `{S // ColumnConvex S ∧ FourConnected S ∧ NoCheckerboard S ∧ S.Nonempty}`。`NoCheckerboard` 是既有实际2×2交替占据排除条件，不包含全局边界单轨道。`ofOrthogonal` 另接受 RowConvex，并调用既有 row-convex+FourConnected 定理提供 NoCheckerboard。

真实 nonempty S 给真实 north 边，所以 `anchor` 是 actual boundary 的 Classical.choose 选择，不是自定义公理。所有边界 Touch path 接既有 genuine succPerm 的 sameCycle 定理，得到 sameCycle_all。succPerm 无固定边由 actual source≠target 证明；IsCycle、support=univ、order=P、所有幂指数<P的枚举双射和 source 顶点枚举单射均随后推出。空集 IsCycle 陷阱已由 Region.Nonempty 排除，没有从空类型的全称结论虚构 anchor。

### 4. 真正的最后一条边与首边闭合

`OrthogonalBoundaryPolygon.rotate_val` 对 n=0 以 Fin.elim0 正确排除不存在的 index；n>0 时最后 index 的 val+1=n，确实回0，其余+1。`facetAt_next` 的 wrap 分支使用已证明 perimeter 次返回 anchor，非wrap使用 successor 幂递推；不是直接假定循环索引几何正确。

vertex_next 把旋转后 source 接到当前真实 target。facetAt_bijective 覆盖全部 actual half-edge，因此 polygon.boundary 是全部真实闭线段并集，不只格角集合。source 顶点枚举单射及既有实际格边交点仅在端点，引出非相邻全线段 disjoint；没有仅凭多边形数据结构名称就宣称简单。

### 5. 连续全遍历与半开周期单射

`trace` 明确逐段 glue 仿射实线段；每个整数接点由真实 consecutive_endpoints 保证相等，因此 global Continuous 成立。闭合由 perimeter 次 successor 返回得到。`trace_piece_final` 把每条实际边的整个0≤u≤1实段纳入，`trace_image` 处理最终t=P端点和其余floor分段，完整像等于 polygon.boundary。

`trace_injective_Ico` 使用0≤u<1分段：同一边由一般 segmentPoint_injective；不同边若像相等，实际格边交点性质迫使两边均在端点，u<1/v<1排除 target，于是两者都为 source，和真实顶点枚举单射矛盾。相邻边的共同点只出现一次，没有漏掉最后/第一边接点。归一 curve 的单射需 P>0，代码从真实 perimeter_pos 获取。

### 6. genuine Euclidean 全分割弧长和原单位尺度

`OrthogonalContourLength` 使用既有 `EuclideanPlane := EuclideanSpace Real (Fin 2)`，不是 Plane=Real×Real 的 product max metric。`unitEuclidean p=(p.x/2,p.y/2)` 将工作坐标side2变成原单位边。真实 unitSegment 对实参数是 Isometry，每段 eVariationOn=1。

核对 mathlib 实际定义：eVariationOn 是对全部有限单调参数序列距离和的上确界；`eVariationOn.sum'` 对单调分点序列给出相邻 Icc variation 的精确有限可加性。因此全长度=P不是只选格角 partition 得到的下界。这里没有假定几何总长度恰为边数，而是使用一般variation工具及单边等距证明。

`OrthogonalPhysicalContour.polygon_boundary_eq_frontier` 接既有任意有限真实集合的 frontier⇔全暴露closedSegment等价；`physicalTrace_image` 再经 actual halfScale homeomorphism 的 frontier运输覆盖整个实际unitRegion frontier。半开单射和连续闭合一并运输，得到实际物理frontier的一条简单连续闭曲线。`euclidean_physicalTrace` 为 rfl，说明半尺度只使用一次，原格边物理长度1；没有double-half。

最后 physicalTrace_length_eq_minimum_rectangle 另显式需要 RowConvex R.val，并结合Region内列凸/四邻连通/非空接已有真实min框定理，识别弧长=原单位最小矩形周长。一般column-convex但非row-convex集合仍能有简单闭frontier，但此处不对它们强行宣称长度=min框周长。

### 7. 真正补上原几何 Good 的严格退出前动态桥接

已继续读取 `ProtectedGeometricGood.lean` 的六条声明。它直接使用既有 `ClippedInitialContour.GeometricGood`，没有改写或削弱该定义。`geometricGood_of_shape` 以真实 innerDiamond 中原点得非空 S，从 Shape 的实际 RowConvex/ColumnConvex/FourConnected 构造 Region；Stable 接既有真实 cleanup fixed-point 定理。实际 min/max 坐标框、全frontier最小性、正周期 m=P、连续闭 physicalTrace、半开周期单射、完整 actualfrontier像和真正Euclidean全分割variation依次填入现存GeometricGood的所有字段。

`actual_modifiedStep_geometricGood` 要求更新前 Shape、D保留、clip支持及 L≥2，并显式要求该次真实 modifiedStep 更新后仍含 innerDiamond。这是目标Good自身包含D的必要输入，代码没有借它假设单cycle/曲线/概率目标；也没有宣称任意更新无条件保留Good。

`protected_preserved_before_exit` 使用实际 `exitTime_le_nat_iff`：如果 n 时刻缺失保护点，则实际首退出≤n，与严格 n<exit 矛盾。`modifiedTrajectory_geometricGood_before_exit` 先用已验收 Shape-upto-exit（允许≤）取得当前Shape及支持，再以严格 n<exit 推当前 protectedSites 保留，经实际 innerDiamond⊆protectedSites 得D保留，调用一般几何桥。stopped版本先使用实际 `stoppedTrajectory_before_exit` 等式，回到同一个真实 modifiedTrajectory；初态版本接实际 clipped_shape。

这次因此真正填补了一般真实frontier简单闭曲线、genuineEuclidean弧长和**严格退出前**的Good动态接口，已不只是P计数。必须保留时间边界：旧Shape可以到且包括退出事件，但这里Good仅对 n<exit 保证；首退出时保护域可能已经损失，不能将严格不等号改成≤或声称退出后冻结形状依然Good。全部是事件索引 n；exit保持ℕ∞，代码未将∞转为0，若exit=∞则每个有限n都在正确的退出前作用域。这里没有提供物理停时分布或生成元。

## 信任、当前限制与后续证据

实际八源文本检查未发现 sorry/admit、自定义 axiom、unsafe、native_decide 或 implemented_by。现已进一步独立核全部114新增命名声明的实际公理输出及源冻结绑定、全部2076分析定理输出和126核心输出，只见Classical.choice、Quot.sound、propext；标准trust0与统一构建记录退出0。当前161份正式源逐字节哈希匹配，144个旧分析证明模块及8核心源未变。没有重复启动构建。

本阶段源码现已包含一般单cycle、真实frontier简单闭curve、Euclidean全分割长度，以及既有GeometricGood的严格退出前动态连接；不再将它们列作此八模块里“没有写出的声明”。实际物理停止law/生成元、CMST/FSS核心概率、重启及原模型最终二次恢复主定理仍未完成。不能把确定性形状不变量、拓扑轮廓或事件索引当作物理概率结论。

方法账本见[19日记录](../../research/followup/METHOD_LEDGER_2026-10-19.md)。本记录不作原创性认证、不联系作者、不公开发布；有限样本只排错。

## 最终验收证据绑定

- 专项 `orthogonal-boundary-stage-declarations-validation.json` 时间2026-10-19T20:34:58.681526+08:00，114名与8源源码声明逐项匹配，114项实际log完整且无重名遗漏，build/audit退出0、trust=0、零新增Lean warning。
- 全局 `analysis-validation.json` 时间2026-10-19T20:36:00.547274+08:00，2076 theorem、公理输出与实际生成的AnalysisAxioms逐项精确匹配，153分析源集与磁盘文件集合完全相同，全部源SHA匹配；标准3公理，无sorryAx/error。
- 核心历史成功记录继续复用，但本次独立重核全部8源码hash与126项原实际输出；无来源偷换。144个旧分析证明模块hash保持，恰新增8个模块；入口变化另记录机读证据。
- 该阶段发现一处历史入口注释笼统写General Good未证，已通知根代理；后续冻结时钟阶段根代理修正它，并通过2026-10-19T20:47:19的必要统一构建/内核重验真实绑定。本报告该阶段161源/2076的历史记录保留，新阶段为163源/2109。注释不改变定理statement，尚缺物理停止law与核心概率。

最终判断：新增确定性一般frontier/完整Euclidean弧长/严格退出前Good阶段已满足本次内部验收，未发现形式化作用域漏洞；完整主定理仍未完成，独立AI不能冒充人类专家认证。
