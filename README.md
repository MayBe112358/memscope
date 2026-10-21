# 内存显微镜 · memscope

在浏览器里**一步一步**运行代码，看清每一步之后**栈、堆、指针和数据结构**变成了什么样。专为学习数据结构设计。

**在线使用：** https://maybe112358.github.io/memscope/

## 支持的语言

| 语言 | 说明 |
| --- | --- |
| C | 指针、`malloc`/`free`、结构体、数组、字符串、`cs50.h`（`get_int`、`get_string` 等） |
| C++ | 类、引用、`new`/`delete`、模板、STL 容器（`vector`、`map`、`set`、`stack`、`queue`、`priority_queue`…） |
| Java | 类与对象、数组、`ArrayList`、`HashMap`、`LinkedList`、`PriorityQueue`、`Scanner` 等 |
| Python | 类、`dataclass`、列表/字典/集合、`collections`、`heapq`、生成器等常用功能 |
| JavaScript / TypeScript | 类、闭包、`Map`/`Set`、原型，TS 的类型标注会被忽略后运行 |

所有代码都由自带的解释器在浏览器里执行，不需要联网，也不需要安装编译器。

## 功能

- **单步调试**：上一步 / 下一步、步过、步出、自动播放，可以随时往回退
- **断点**：点击行号设置断点（或按 F8 跳到下一个断点）
- **可视化**
  - 链表横向排开，二叉树按树形排布，哈希表画成「指针数组 + 链」
  - 二维数组画成带行列号的矩阵；布尔 / 0-1 邻接矩阵会同时画成一张图
  - 优先队列（堆）同时显示为完全二叉树
  - `i`、`j`、`lo`、`hi` 等下标变量会标在对应的数组格子上
  - 每一步发生变化的值会高亮
- **环境图模式（CS61A 风格）**：Python / JavaScript 中，每个帧标出编号和父帧 `f2: g [parent=f1]`，函数画成对象 `func h(x) [parent=f2]`，已返回的帧变灰保留；查找自由变量、`nonlocal` 修改时会说明沿父帧找到了哪里。遇到高阶函数、闭包、lambda 时自动开启，也可以在状态栏一键切换
- **C 语言错误检测**：空指针、野指针、释放后使用、数组越界、读取未初始化变量、内存泄漏，都会给出中文解释
- **输入**：可以填写命令行参数和标准输入
- **40+ 个内置示例**：高阶函数与闭包（make_adder、compose、柯里化、计数器）、CS50 Tideman / Inheritance、链表、BST、Trie、哈希表、图的 BFS/DFS、Dijkstra、并查集、拓扑排序、排序与递归……

## 键盘快捷键

| 按键 | 作用 |
| --- | --- |
| `Ctrl/⌘ + Enter` | 运行 |
| `←` / `→` | 上一步 / 下一步（`Shift` 一次走 10 步） |
| `F10` / `F11` / `Shift+F11` | 步过 / 步入 / 步出 |
| `F8` | 跳到下一个断点 |
| `空格` | 播放 / 暂停 |

## 本地开发

```bash
npm run build   # 把 src/ 拼成单文件 index.html
npm test        # 运行全部内置示例，检查是否都能正确执行
node test/run.js c path/to/main.c "args=1 2 3"   # 用命令行跑单个程序
```

目录结构：

```
src/
  core.js            公共：执行记录、错误类型、printf 格式化
  clike_*.js         C / C++ / Java：词法、语法、解释器、标准库、快照
  py_*.js            Python：语法、解释器、内置函数与模块
  js_*.js            JavaScript / TypeScript：语法、解释器、内置对象
  examples.js        内置示例
  editor.js          代码编辑器（高亮、断点）
  viz.js             可视化渲染（栈、堆、箭头、布局）
  app.js             界面控制
  shell.html         页面结构与样式
```

## 局限

- 每种语言只实现了教学中常用的语法子集
- 不支持 `async` / 多线程；生成器会一次性算完，不能单步观察它暂停和恢复
- 为了保证流畅，默认最多记录 5000 步（可在设置里调高）
