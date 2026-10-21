// ===== Example programs =====
(function (G) {
  const DSV = G.DSV;
  const E = [];
  const add = (lang, id, title, code, extra) => E.push(Object.assign({ lang, id, title, code: code.replace(/^\n/, '') }, extra || {}));

  // ======================= C =======================
  add('c', 'c-tideman', 'CS50 Tideman：锁定图与 DFS 判环', `
// CS50 Tideman：用“锁定图”选出胜者
// 核心：lock_pairs 按强度依次加边，creates_cycle 用 DFS 判断加边后是否成环
// 提示：在 creates_cycle 里打个断点，看递归怎样沿着 locked 里的边往下走

#include <cs50.h>
#include <stdio.h>
#include <string.h>

// CS50 原题是 9；这里改成 3，画面更清楚（想要更多候选人就把它改大）
#define MAX 3

// preferences[i][j]：更喜欢 i 胜过 j 的选民人数
int preferences[MAX][MAX];

// locked[i][j] == true 表示图里有一条边 i -> j
bool locked[MAX][MAX];

typedef struct
{
    int winner;
    int loser;
}
pair;

string candidates[MAX];
pair pairs[MAX * (MAX - 1) / 2];

int pair_count;
int candidate_count;

bool vote(int rank, string name, int ranks[]);
void record_preferences(int ranks[]);
void add_pairs(void);
void sort_pairs(void);
void lock_pairs(void);
bool creates_cycle(int winner, int loser);
void print_winner(void);

int main(int argc, string argv[])
{
    if (argc < 2)
    {
        printf("Usage: tideman [candidate ...]\\n");
        return 1;
    }

    candidate_count = argc - 1;
    if (candidate_count > MAX)
    {
        printf("Maximum number of candidates is %i\\n", MAX);
        return 2;
    }
    for (int i = 0; i < candidate_count; i++)
    {
        candidates[i] = argv[i + 1];
    }

    pair_count = 0;
    int voter_count = get_int("Number of voters: ");

    for (int i = 0; i < voter_count; i++)
    {
        // ranks[i] 是该选民第 i 喜欢的候选人编号
        int ranks[MAX];
        for (int j = 0; j < candidate_count; j++)
        {
            string name = get_string("Rank %i: ", j + 1);
            if (!vote(j, name, ranks))
            {
                printf("Invalid vote.\\n");
                return 3;
            }
        }
        record_preferences(ranks);
    }

    add_pairs();
    sort_pairs();
    lock_pairs();
    print_winner();
    return 0;
}

bool vote(int rank, string name, int ranks[])
{
    for (int i = 0; i < candidate_count; i++)
    {
        if (strcmp(candidates[i], name) == 0)
        {
            ranks[rank] = i;
            return true;
        }
    }
    return false;
}

void record_preferences(int ranks[])
{
    for (int i = 0; i < candidate_count; i++)
    {
        for (int j = i + 1; j < candidate_count; j++)
        {
            preferences[ranks[i]][ranks[j]]++;
        }
    }
}

void add_pairs(void)
{
    for (int i = 0; i < candidate_count; i++)
    {
        for (int j = i + 1; j < candidate_count; j++)
        {
            if (preferences[i][j] > preferences[j][i])
            {
                pairs[pair_count].winner = i;
                pairs[pair_count].loser = j;
                pair_count++;
            }
            else if (preferences[j][i] > preferences[i][j])
            {
                pairs[pair_count].winner = j;
                pairs[pair_count].loser = i;
                pair_count++;
            }
        }
    }
}

// 按胜出强度从大到小排序（选择排序）
void sort_pairs(void)
{
    for (int i = 0; i < pair_count - 1; i++)
    {
        int best = i;
        for (int j = i + 1; j < pair_count; j++)
        {
            int s_j = preferences[pairs[j].winner][pairs[j].loser];
            int s_best = preferences[pairs[best].winner][pairs[best].loser];
            if (s_j > s_best)
            {
                best = j;
            }
        }
        pair tmp = pairs[i];
        pairs[i] = pairs[best];
        pairs[best] = tmp;
    }
}

// 如果加上边 winner -> loser，能不能从 loser 沿着已锁定的边走回 winner？
bool creates_cycle(int winner, int loser)
{
    if (loser == winner)
    {
        return true;   // 绕回起点：成环
    }
    for (int i = 0; i < candidate_count; i++)
    {
        if (locked[loser][i])
        {
            if (creates_cycle(winner, i))
            {
                return true;
            }
        }
    }
    return false;
}

void lock_pairs(void)
{
    for (int i = 0; i < pair_count; i++)
    {
        if (!creates_cycle(pairs[i].winner, pairs[i].loser))
        {
            locked[pairs[i].winner][pairs[i].loser] = true;
        }
    }
}

// 胜者是图的“源头”：没有任何边指向它
void print_winner(void)
{
    for (int i = 0; i < candidate_count; i++)
    {
        bool is_source = true;
        for (int j = 0; j < candidate_count; j++)
        {
            if (locked[j][i])
            {
                is_source = false;
                break;
            }
        }
        if (is_source)
        {
            printf("%s\\n", candidates[i]);
            return;
        }
    }
}
`, { args: 'Alice Bob Charlie', stdin: '5\nAlice\nBob\nCharlie\nAlice\nBob\nCharlie\nBob\nCharlie\nAlice\nBob\nCharlie\nAlice\nCharlie\nAlice\nBob', desc: 'locked 就是图的邻接矩阵（true = 一条边）。lock_pairs 每加一条边前，creates_cycle 都会顺着已有的边做 DFS：看左边调用栈一层层加深，走回 winner 就说明成环，这条边被跳过。' });

  add('c', 'c-list-argv', '链表：用命令行参数构建（尾插法）', `
// 使用链表实现数字列表（CS50 课上的例子）
// 运行参数在下方“命令行参数”里修改

#include <cs50.h>
#include <stdio.h>
#include <stdlib.h>

typedef struct node
{
    int number;
    struct node *next;
}
node;

int main(int argc, char *argv[])
{
    // Memory for numbers
    node *list = NULL;

    // For each command-line argument
    for (int i = 1; i < argc; i++)
    {
        // Convert argument to int
        int number = atoi(argv[i]);

        // Allocate node for number
        node *n = malloc(sizeof(node));
        if (n == NULL)
        {
            return 1;
        }
        n->number = number;
        n->next = NULL;

        // If list is empty
        if (list == NULL)
        {
            // This node is the whole list
            list = n;
        }

        // If list has numbers already
        else
        {
            // Iterate over nodes in list
            for (node *ptr = list; ptr != NULL; ptr = ptr->next)
            {
                // If at end of list
                if (ptr->next == NULL)
                {
                    // Append node
                    ptr->next = n;
                    break;
                }
            }
        }
    }

    // Print numbers
    for (node *ptr = list; ptr != NULL; ptr = ptr->next)
    {
        printf("%i\\n", ptr->number);
    }

    // Free memory
    node *ptr = list;
    while (ptr != NULL)
    {
        node *next = ptr->next;
        free(ptr);
        ptr = next;
    }
}
`, { args: '1 2 3', desc: '每次 malloc 一个节点，再从头走到尾把它接上。注意看 ptr 是怎样一步步往后移动的。' });

  add('c', 'c-list-ops', '链表：头插、删除与反转', `
#include <stdio.h>
#include <stdlib.h>

typedef struct node
{
    int value;
    struct node *next;
} node;

// 头插法：新节点成为新的头
node *prepend(node *head, int value)
{
    node *n = malloc(sizeof(node));
    n->value = value;
    n->next = head;
    return n;
}

// 删除第一个值为 target 的节点
node *delete(node *head, int target)
{
    node *prev = NULL;
    node *cur = head;
    while (cur != NULL && cur->value != target)
    {
        prev = cur;
        cur = cur->next;
    }
    if (cur == NULL)
    {
        return head;            // 没找到
    }
    if (prev == NULL)
    {
        head = cur->next;       // 删除的是头节点
    }
    else
    {
        prev->next = cur->next; // 跳过 cur
    }
    free(cur);
    return head;
}

// 原地反转链表
node *reverse(node *head)
{
    node *prev = NULL;
    while (head != NULL)
    {
        node *next = head->next;
        head->next = prev;
        prev = head;
        head = next;
    }
    return prev;
}

int main(void)
{
    node *list = NULL;
    for (int i = 1; i <= 4; i++)
    {
        list = prepend(list, i * 10);
    }
    list = delete(list, 20);
    list = reverse(list);

    for (node *p = list; p != NULL; p = p->next)
    {
        printf("%d ", p->value);
    }
    printf("\\n");

    while (list != NULL)
    {
        node *tmp = list->next;
        free(list);
        list = tmp;
    }
    return 0;
}
`, { desc: '反转时盯住 prev、head、next 三个指针：每一步只改一根 next。' });

  add('c', 'c-bst', '二叉搜索树：递归插入、遍历与释放', `
#include <stdio.h>
#include <stdlib.h>

typedef struct node
{
    int number;
    struct node *left;
    struct node *right;
} node;

node *insert(node *tree, int number)
{
    if (tree == NULL)
    {
        node *n = malloc(sizeof(node));
        n->number = number;
        n->left = NULL;
        n->right = NULL;
        return n;
    }
    if (number < tree->number)
    {
        tree->left = insert(tree->left, number);
    }
    else
    {
        tree->right = insert(tree->right, number);
    }
    return tree;
}

int search(node *tree, int number)
{
    if (tree == NULL)
    {
        return 0;
    }
    else if (number < tree->number)
    {
        return search(tree->left, number);
    }
    else if (number > tree->number)
    {
        return search(tree->right, number);
    }
    return 1;
}

void print_tree(node *root)
{
    if (root == NULL)
    {
        return;
    }
    print_tree(root->left);
    printf("%i ", root->number);
    print_tree(root->right);
}

void free_tree(node *root)
{
    if (root == NULL)
    {
        return;
    }
    free_tree(root->left);
    free_tree(root->right);
    free(root);
}

int main(void)
{
    node *tree = NULL;
    int values[] = {4, 2, 6, 1, 3, 5, 7};
    for (int i = 0; i < 7; i++)
    {
        tree = insert(tree, values[i]);
    }
    printf("found 5? %i\\n", search(tree, 5));
    print_tree(tree);
    printf("\\n");
    free_tree(tree);
}
`, { desc: '左边的调用栈会随着递归一层层变深；右边按“中序”排开，节点从左到右正好是排好序的。' });

  add('c', 'c-hash', '哈希表：拉链法（CS50 speller 风格）', `
#include <ctype.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <strings.h>

#define LENGTH 15

typedef struct node
{
    char word[LENGTH + 1];
    struct node *next;
} node;

// 桶的个数（为了看得清楚，故意取得很小）
const unsigned int N = 4;
node *table[N];

unsigned int hash(const char *word)
{
    return (toupper(word[0]) - 'A') % N;
}

bool load_word(const char *word)
{
    node *n = malloc(sizeof(node));
    if (n == NULL)
    {
        return false;
    }
    strcpy(n->word, word);
    unsigned int h = hash(word);
    n->next = table[h];   // 插到这个桶的链表头部
    table[h] = n;
    return true;
}

bool check(const char *word)
{
    for (node *cursor = table[hash(word)]; cursor != NULL; cursor = cursor->next)
    {
        if (strcasecmp(cursor->word, word) == 0)
        {
            return true;
        }
    }
    return false;
}

bool unload(void)
{
    for (int i = 0; i < N; i++)
    {
        node *cursor = table[i];
        while (cursor != NULL)
        {
            node *tmp = cursor;
            cursor = cursor->next;
            free(tmp);
        }
        table[i] = NULL;
    }
    return true;
}

int main(void)
{
    char *words[] = {"apple", "bat", "cat", "dog", "egg", "fig", "ant"};
    for (int i = 0; i < 7; i++)
    {
        load_word(words[i]);
    }
    printf("Cat? %s\\n", check("Cat") ? "yes" : "no");
    printf("cow? %s\\n", check("cow") ? "yes" : "no");
    unload();
}
`, { desc: 'table 是一个全局的指针数组，每个桶挂着一条链表。注意 C 语言里全局数组会被自动初始化为 NULL。' });

  add('c', 'c-trie', '字典树 Trie', `
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>

typedef struct node
{
    bool is_word;
    struct node *children[26];
} node;

node *new_node(void)
{
    node *n = malloc(sizeof(node));
    n->is_word = false;
    for (int i = 0; i < 26; i++)
    {
        n->children[i] = NULL;
    }
    return n;
}

void insert(node *root, const char *word)
{
    node *cur = root;
    for (int i = 0; word[i] != '\\0'; i++)
    {
        int index = word[i] - 'a';
        if (cur->children[index] == NULL)
        {
            cur->children[index] = new_node();
        }
        cur = cur->children[index];
    }
    cur->is_word = true;
}

bool contains(node *root, const char *word)
{
    node *cur = root;
    for (int i = 0; word[i] != '\\0'; i++)
    {
        cur = cur->children[word[i] - 'a'];
        if (cur == NULL)
        {
            return false;
        }
    }
    return cur->is_word;
}

void destroy(node *n)
{
    for (int i = 0; i < 26; i++)
    {
        if (n->children[i] != NULL)
        {
            destroy(n->children[i]);
        }
    }
    free(n);
}

int main(void)
{
    node *root = new_node();
    insert(root, "cat");
    insert(root, "car");
    insert(root, "do");
    printf("car: %d, ca: %d\\n", contains(root, "car"), contains(root, "ca"));
    destroy(root);
}
`, { desc: '每个节点有 26 个孩子指针（a~z）。连续的 NULL 会被折叠显示，可以在设置里关闭折叠。' });

  add('c', 'c-stack-queue', '栈与循环队列（数组实现）', `
#include <stdio.h>
#include <stdbool.h>

#define CAPACITY 5

typedef struct
{
    int items[CAPACITY];
    int top;
} stack;

typedef struct
{
    int items[CAPACITY];
    int front;
    int size;
} queue;

bool push(stack *s, int x)
{
    if (s->top == CAPACITY - 1)
    {
        return false;
    }
    s->top++;
    s->items[s->top] = x;
    return true;
}

int pop(stack *s)
{
    return s->items[s->top--];
}

bool enqueue(queue *q, int x)
{
    if (q->size == CAPACITY)
    {
        return false;
    }
    int rear = (q->front + q->size) % CAPACITY;
    q->items[rear] = x;
    q->size++;
    return true;
}

int dequeue(queue *q)
{
    int x = q->items[q->front];
    q->front = (q->front + 1) % CAPACITY;
    q->size--;
    return x;
}

int main(void)
{
    stack s;
    s.top = -1;
    push(&s, 1);
    push(&s, 2);
    push(&s, 3);
    printf("pop: %d\\n", pop(&s));

    queue q = {{0}, 0, 0};
    for (int i = 1; i <= 5; i++)
    {
        enqueue(&q, i * 10);
    }
    dequeue(&q);
    dequeue(&q);
    enqueue(&q, 60);   // 绕回数组开头
    enqueue(&q, 70);
    while (q.size > 0)
    {
        printf("%d ", dequeue(&q));
    }
    printf("\\n");
}
`, { desc: 's 和 q 是 main 里的局部结构体，直接画在栈帧里。push 收到的是它们的地址（&s），所以箭头指回 main 的变量。注意 s.items 一开始是未初始化的“?”。' });

  add('c', 'c-pointers', '指针基础：& 和 *、swap、数组与指针', `
#include <stdio.h>

void swap_wrong(int a, int b)
{
    int tmp = a;
    a = b;
    b = tmp;
}

void swap(int *a, int *b)
{
    int tmp = *a;
    *a = *b;
    *b = tmp;
}

int main(void)
{
    int x = 1;
    int y = 2;
    int *p = &x;      // p 保存 x 的地址
    *p = 10;          // 通过 p 修改 x

    swap_wrong(x, y); // 传的是值的副本，x 和 y 不会变
    printf("after swap_wrong: x=%i y=%i\\n", x, y);
    swap(&x, &y);     // 传的是地址
    printf("after swap: x=%i y=%i\\n", x, y);

    int numbers[] = {4, 8, 15, 16, 23};
    int *q = numbers;         // 数组名会“退化”成指向第 0 个元素的指针
    q = q + 2;                // 指针算术：往后移动 2 个 int
    printf("*q = %i, q[1] = %i\\n", *q, q[1]);

    char *s = "HI!";
    printf("%c%c%c\\n", *s, *(s + 1), s[2]);
}
`, { desc: '在设置里打开“显示内存地址”，可以看到每个变量和指针的地址（模拟 64 位系统）。' });

  add('c', 'c-errors', '常见错误：内存泄漏、垃圾值、释放后使用', `
#include <stdio.h>
#include <stdlib.h>

int main(void)
{
    // 1. 垃圾值：变量没有初始化就使用
    int scores[3];
    printf("%i\\n", scores[1]);

    // 2. 内存泄漏：把唯一指向这块内存的指针改掉了
    int *a = malloc(3 * sizeof(int));
    a[0] = 1;
    a = malloc(3 * sizeof(int));   // 第一块内存再也找不到了

    // 3. 释放后使用
    a[0] = 7;
    free(a);
    printf("%i\\n", a[0]);          // a 已经是悬空指针
}
`, { desc: '一步步执行，注意右边红色的“泄漏”标记和最后的报错说明。' });

  add('c', 'c-sort', '归并排序（递归 + 临时数组）', `
#include <stdio.h>

void merge(int arr[], int lo, int mid, int hi)
{
    int tmp[8];
    int i = lo, j = mid + 1, k = 0;
    while (i <= mid && j <= hi)
    {
        if (arr[i] <= arr[j])
        {
            tmp[k++] = arr[i++];
        }
        else
        {
            tmp[k++] = arr[j++];
        }
    }
    while (i <= mid)
    {
        tmp[k++] = arr[i++];
    }
    while (j <= hi)
    {
        tmp[k++] = arr[j++];
    }
    for (int t = 0; t < k; t++)
    {
        arr[lo + t] = tmp[t];
    }
}

void merge_sort(int arr[], int lo, int hi)
{
    if (lo >= hi)
    {
        return;
    }
    int mid = (lo + hi) / 2;
    merge_sort(arr, lo, mid);
    merge_sort(arr, mid + 1, hi);
    merge(arr, lo, mid, hi);
}

int main(void)
{
    int numbers[] = {5, 2, 7, 4, 1, 6, 3, 0};
    merge_sort(numbers, 0, 7);
    for (int i = 0; i < 8; i++)
    {
        printf("%i ", numbers[i]);
    }
    printf("\\n");
}
`, { desc: 'arr 参数其实是一个指针，指回 main 里的 numbers。i、j、k、lo、hi 这些下标变量会直接标在数组格子下面。' });

  add('c', 'c-recursion', '递归：阶乘与调用栈', `
#include <stdio.h>

int factorial(int n)
{
    if (n <= 1)
    {
        return 1;            // 基本情况（base case）
    }
    return n * factorial(n - 1);
}

int main(void)
{
    int result = factorial(5);
    printf("5! = %i\\n", result);
}
`, { desc: '每一次调用都会在栈上新开一个帧；返回时，帧底部会显示返回值。' });

  add('c', 'c-input', '读取输入：get_int / get_string', `
#include <cs50.h>
#include <stdio.h>
#include <string.h>

int main(void)
{
    string name = get_string("What's your name? ");
    int n = get_int("How many times? ");
    for (int i = 0; i < n; i++)
    {
        printf("hello, %s\\n", name);
    }
    printf("name has %lu letters\\n", strlen(name));
}
`, { stdin: 'David\n3', desc: '程序读取的内容来自下方的“标准输入”框，每行一个值。' });

  // ======================= C++ =======================
  add('cpp', 'cpp-list', '链表类：构造、析构与 new / delete', `
#include <iostream>
using namespace std;

struct Node {
    int val;
    Node* next;
    Node(int v) : val(v), next(nullptr) {}
};

class LinkedList {
    Node* head = nullptr;
    int size = 0;
public:
    ~LinkedList() {
        Node* cur = head;
        while (cur) {
            Node* next = cur->next;
            delete cur;
            cur = next;
        }
    }
    void pushFront(int v) {
        Node* n = new Node(v);
        n->next = head;
        head = n;
        size++;
    }
    void pushBack(int v) {
        Node* n = new Node(v);
        if (!head) { head = n; size++; return; }
        Node* cur = head;
        while (cur->next) cur = cur->next;
        cur->next = n;
        size++;
    }
    void print() const {
        for (Node* p = head; p; p = p->next) cout << p->val << " -> ";
        cout << "null (size " << size << ")" << endl;
    }
};

int main() {
    LinkedList list;
    list.pushBack(2);
    list.pushFront(1);
    list.pushBack(3);
    list.print();
    return 0;   // list 离开作用域时会自动调用析构函数
}
`, { desc: 'main 结束时，局部对象 list 的析构函数会被自动调用，逐个 delete 节点——看看最后有没有内存泄漏。' });

  add('cpp', 'cpp-stl', 'STL 容器：vector / stack / queue / map', `
#include <iostream>
#include <vector>
#include <stack>
#include <queue>
#include <map>
#include <string>
using namespace std;

int main() {
    vector<int> v;
    for (int i = 1; i <= 5; i++) {
        v.push_back(i * i);     // 注意观察 capacity 的翻倍
    }
    v.pop_back();

    stack<char> st;
    string s = "({[]})";
    bool ok = true;
    for (char c : s) {
        if (c == '(' || c == '[' || c == '{') st.push(c);
        else {
            char open = st.top();
            st.pop();
            if ((c == ')' && open != '(') || (c == ']' && open != '[')) ok = false;
        }
    }
    cout << "balanced: " << (ok && st.empty()) << endl;

    queue<int> q;
    q.push(1); q.push(2); q.push(3);
    q.pop();

    map<string, int> count;
    for (string w : {"to", "be", "or", "not", "to", "be"}) {
        count[w]++;
    }
    for (auto& p : count) cout << p.first << "=" << p.second << " ";
    cout << endl;
}
`, { desc: 'vector 变量本身在栈上，它的元素在堆上——这就是箭头的含义。map 会自动按键排序。' });

  add('cpp', 'cpp-bst', '二叉搜索树（模板类 + 递归）', `
#include <iostream>
using namespace std;

template <typename T>
class BST {
    struct Node {
        T key;
        Node* left;
        Node* right;
        Node(T k) : key(k), left(nullptr), right(nullptr) {}
    };
    Node* root = nullptr;

    Node* insert(Node* n, T key) {
        if (n == nullptr) return new Node(key);
        if (key < n->key) n->left = insert(n->left, key);
        else if (key > n->key) n->right = insert(n->right, key);
        return n;
    }
    int height(Node* n) {
        if (!n) return 0;
        return 1 + max(height(n->left), height(n->right));
    }
    void destroy(Node* n) {
        if (!n) return;
        destroy(n->left);
        destroy(n->right);
        delete n;
    }
public:
    void insert(T key) { root = insert(root, key); }
    int height() { return height(root); }
    ~BST() { destroy(root); }
};

int main() {
    BST<int> tree;
    for (int x : {8, 3, 10, 1, 6, 14, 4, 7}) tree.insert(x);
    cout << "height = " << tree.height() << endl;
}
`);

  add('cpp', 'cpp-graph', '图的 BFS（邻接表）', `
#include <iostream>
#include <vector>
#include <queue>
using namespace std;

int main() {
    int n = 6;
    vector<vector<int>> adj(n);
    int edges[][2] = {{0, 1}, {0, 2}, {1, 3}, {2, 4}, {3, 5}, {4, 5}};
    for (auto& e : edges) {
        adj[e[0]].push_back(e[1]);
        adj[e[1]].push_back(e[0]);
    }

    vector<int> dist(n, -1);
    queue<int> q;
    dist[0] = 0;
    q.push(0);
    while (!q.empty()) {
        int u = q.front();
        q.pop();
        for (int v : adj[u]) {
            if (dist[v] == -1) {
                dist[v] = dist[u] + 1;
                q.push(v);
            }
        }
    }
    for (int i = 0; i < n; i++) cout << i << ":" << dist[i] << " ";
    cout << endl;
}
`, { desc: 'adj 是“vector 的 vector”：外层每个格子都指向一个内层 vector，像一张表。' });

  add('cpp', 'cpp-ref', '值传递、指针传递与引用传递', `
#include <iostream>
#include <vector>
using namespace std;

void byValue(vector<int> v) { v.push_back(99); }
void byPointer(vector<int>* v) { v->push_back(1); }
void byReference(vector<int>& v) { v.push_back(2); }

int main() {
    vector<int> nums = {0};
    byValue(nums);      // 函数里改的是一份副本
    byPointer(&nums);
    byReference(nums);  // v 只是 nums 的另一个名字（虚线箭头）
    cout << nums.size() << endl;
}
`, { desc: '进入 byValue 时，堆上会多出一个 vector 的副本；byReference 的参数用虚线箭头表示“别名”。' });

  // ======================= Java =======================
  add('java', 'java-list', '链表：节点类与反转', `
public class Main {
    static class Node {
        int val;
        Node next;
        Node(int val) { this.val = val; }
    }

    static Node reverse(Node head) {
        Node prev = null;
        Node cur = head;
        while (cur != null) {
            Node next = cur.next;
            cur.next = prev;
            prev = cur;
            cur = next;
        }
        return prev;
    }

    public static void main(String[] args) {
        Node head = new Node(1);
        head.next = new Node(2);
        head.next.next = new Node(3);
        head = reverse(head);
        for (Node p = head; p != null; p = p.next) {
            System.out.print(p.val + " ");
        }
        System.out.println();
    }
}
`, { desc: 'Java 的对象变量保存的都是“引用”（箭头）。没有引用指向的对象会被垃圾回收，从画面上消失。' });

  add('java', 'java-stack-queue', '栈与队列：括号匹配 + 层序队列', `
import java.util.*;

public class Main {
    static boolean isValid(String s) {
        Deque<Character> stack = new ArrayDeque<>();
        for (char c : s.toCharArray()) {
            if (c == '(' || c == '[' || c == '{') {
                stack.push(c);
            } else {
                if (stack.isEmpty()) return false;
                char open = stack.pop();
                if (c == ')' && open != '(') return false;
                if (c == ']' && open != '[') return false;
                if (c == '}' && open != '{') return false;
            }
        }
        return stack.isEmpty();
    }

    public static void main(String[] args) {
        System.out.println(isValid("{[()]}"));
        System.out.println(isValid("([)]"));

        Queue<String> queue = new LinkedList<>();
        queue.offer("Alice");
        queue.offer("Bob");
        queue.offer("Carol");
        while (!queue.isEmpty()) {
            System.out.println("serve " + queue.poll());
        }
    }
}
`);

  add('java', 'java-bst', '二叉搜索树：插入、查找与中序遍历', `
public class BinarySearchTree {
    private static class TreeNode {
        int key;
        TreeNode left, right;
        TreeNode(int key) { this.key = key; }
    }

    private TreeNode root;

    public void insert(int key) {
        root = insert(root, key);
    }

    private TreeNode insert(TreeNode node, int key) {
        if (node == null) return new TreeNode(key);
        if (key < node.key) node.left = insert(node.left, key);
        else if (key > node.key) node.right = insert(node.right, key);
        return node;
    }

    public boolean contains(int key) {
        TreeNode cur = root;
        while (cur != null) {
            if (key == cur.key) return true;
            cur = key < cur.key ? cur.left : cur.right;
        }
        return false;
    }

    private void inorder(TreeNode node, StringBuilder sb) {
        if (node == null) return;
        inorder(node.left, sb);
        sb.append(node.key).append(' ');
        inorder(node.right, sb);
    }

    public static void main(String[] args) {
        BinarySearchTree t = new BinarySearchTree();
        int[] keys = {50, 30, 70, 20, 40, 60, 80};
        for (int k : keys) t.insert(k);
        System.out.println(t.contains(60) + " " + t.contains(65));
        StringBuilder sb = new StringBuilder();
        t.inorder(t.root, sb);
        System.out.println(sb.toString());
    }
}
`);

  add('java', 'java-hashmap', '自己实现哈希表（拉链法）', `
public class MyHashMap {
    static class Entry {
        String key;
        int value;
        Entry next;
        Entry(String key, int value, Entry next) {
            this.key = key;
            this.value = value;
            this.next = next;
        }
    }

    private Entry[] buckets = new Entry[4];
    private int size = 0;

    private int indexFor(String key) {
        return Math.abs(key.hashCode()) % buckets.length;
    }

    public void put(String key, int value) {
        int i = indexFor(key);
        for (Entry e = buckets[i]; e != null; e = e.next) {
            if (e.key.equals(key)) {
                e.value = value;
                return;
            }
        }
        buckets[i] = new Entry(key, value, buckets[i]);
        size++;
    }

    public Integer get(String key) {
        for (Entry e = buckets[indexFor(key)]; e != null; e = e.next) {
            if (e.key.equals(key)) return e.value;
        }
        return null;
    }

    public static void main(String[] args) {
        MyHashMap map = new MyHashMap();
        String[] words = {"apple", "banana", "cherry", "date", "apple"};
        for (String w : words) {
            Integer old = map.get(w);
            map.put(w, old == null ? 1 : old + 1);
        }
        System.out.println(map.get("apple") + " " + map.get("kiwi") + " size=" + map.size);
    }
}
`);

  add('java', 'java-heap', '优先队列与 Top-K', `
import java.util.*;

public class Main {
    public static void main(String[] args) {
        int[] nums = {5, 1, 9, 3, 7, 2, 8};
        int k = 3;
        // 小顶堆里只保留最大的 k 个数
        PriorityQueue<Integer> heap = new PriorityQueue<>();
        for (int x : nums) {
            heap.offer(x);
            if (heap.size() > k) {
                heap.poll();
            }
        }
        List<Integer> top = new ArrayList<>(heap);
        Collections.sort(top, Collections.reverseOrder());
        System.out.println("top " + k + ": " + top);
    }
}
`, { desc: '堆在内部是一个数组；打开设置里的“堆显示为树”，可以同时看到它对应的完全二叉树。' });

  // ======================= Python =======================
  add('python', 'py-list', '链表类：追加、反转与打印', `
class Node:
    def __init__(self, val, next=None):
        self.val = val
        self.next = next


class LinkedList:
    def __init__(self):
        self.head = None
        self.size = 0

    def append(self, val):
        node = Node(val)
        if self.head is None:
            self.head = node
        else:
            cur = self.head
            while cur.next:
                cur = cur.next
            cur.next = node
        self.size += 1

    def reverse(self):
        prev, cur = None, self.head
        while cur:
            nxt = cur.next
            cur.next = prev
            prev = cur
            cur = nxt
        self.head = prev

    def __str__(self):
        parts = []
        cur = self.head
        while cur:
            parts.append(str(cur.val))
            cur = cur.next
        return " -> ".join(parts)


lst = LinkedList()
for x in [1, 2, 3, 4]:
    lst.append(x)
print(lst)
lst.reverse()
print(lst)
`, { desc: 'Python 里变量都是“名字指向对象”。self 就是当前对象，所以方法的帧里会有一个 self 箭头。' });

  add('python', 'py-bst', '二叉搜索树：递归插入与遍历', `
class TreeNode:
    def __init__(self, key):
        self.key = key
        self.left = None
        self.right = None


def insert(root, key):
    if root is None:
        return TreeNode(key)
    if key < root.key:
        root.left = insert(root.left, key)
    else:
        root.right = insert(root.right, key)
    return root


def inorder(root, out):
    if root:
        inorder(root.left, out)
        out.append(root.key)
        inorder(root.right, out)


def height(root):
    if root is None:
        return 0
    return 1 + max(height(root.left), height(root.right))


root = None
for k in [8, 3, 10, 1, 6, 14, 4, 7, 13]:
    root = insert(root, k)

result = []
inorder(root, result)
print(result, "height:", height(root))
`);

  add('python', 'py-bfs', '图的 BFS 与 DFS（字典 + deque）', `
from collections import deque

graph = {
    "A": ["B", "C"],
    "B": ["D", "E"],
    "C": ["F"],
    "D": [],
    "E": ["F"],
    "F": [],
}


def bfs(start):
    visited = {start}
    queue = deque([start])
    order = []
    while queue:
        node = queue.popleft()
        order.append(node)
        for nb in graph[node]:
            if nb not in visited:
                visited.add(nb)
                queue.append(nb)
    return order


def dfs(node, visited=None):
    if visited is None:
        visited = []
    visited.append(node)
    for nb in graph[node]:
        if nb not in visited:
            dfs(nb, visited)
    return visited


print("BFS:", bfs("A"))
print("DFS:", dfs("A"))
`);

  add('python', 'py-sort', '排序：快速排序与归并排序', `
def quick_sort(arr, lo, hi):
    if lo >= hi:
        return
    pivot = arr[hi]
    i = lo
    for j in range(lo, hi):
        if arr[j] < pivot:
            arr[i], arr[j] = arr[j], arr[i]
            i += 1
    arr[i], arr[hi] = arr[hi], arr[i]
    quick_sort(arr, lo, i - 1)
    quick_sort(arr, i + 1, hi)


def merge_sort(nums):
    if len(nums) <= 1:
        return nums
    mid = len(nums) // 2
    left = merge_sort(nums[:mid])
    right = merge_sort(nums[mid:])
    merged = []
    i = j = 0
    while i < len(left) and j < len(right):
        if left[i] <= right[j]:
            merged.append(left[i])
            i += 1
        else:
            merged.append(right[j])
            j += 1
    return merged + left[i:] + right[j:]


data = [5, 2, 8, 1, 9, 3]
quick_sort(data, 0, len(data) - 1)
print(data)
print(merge_sort([4, 1, 3, 2]))
`, { desc: '下标变量 i、j、lo、hi 会标在列表格子下面。注意 merge_sort 里的切片 nums[:mid] 会创建新的列表。' });

  add('python', 'py-dict', '字典与集合：词频统计', `
text = "the quick brown fox jumps over the lazy dog the end"

freq = {}
for word in text.split():
    freq[word] = freq.get(word, 0) + 1

seen = set()
dupes = []
for word in text.split():
    if word in seen and word not in dupes:
        dupes.append(word)
    seen.add(word)

top = sorted(freq.items(), key=lambda kv: -kv[1])[:2]
print(top, dupes, len(seen))
`);

  add('python', 'py-heap', '堆：heapq 与任务调度', `
import heapq

tasks = []
heapq.heappush(tasks, (3, "写报告"))
heapq.heappush(tasks, (1, "修 bug"))
heapq.heappush(tasks, (2, "开会"))
heapq.heappush(tasks, (1, "回邮件"))

while tasks:
    priority, name = heapq.heappop(tasks)
    print(priority, name)
`, { desc: '堆就是一个满足“父节点不大于孩子”的列表。打开设置里的“堆显示为树”可以看到树形。' });

  add('python', 'py-alias', '引用与别名：为什么 b 也变了？', `
a = [1, 2, 3]
b = a            # b 和 a 指向同一个列表
b.append(4)

c = a[:]         # 切片会复制出一个新列表
c.append(5)

grid = [[0] * 3] * 3      # 三行其实是同一个列表！
grid[0][0] = 1

good = [[0] * 3 for _ in range(3)]
good[0][0] = 1

print(a, b, c)
print(grid)
print(good)
`, { desc: '经典陷阱：看 grid 的三个格子是不是都指向同一个列表。' });

  add('python', 'py-recursion', '递归与回溯：全排列', `
def permute(nums):
    result = []
    path = []
    used = [False] * len(nums)

    def backtrack():
        if len(path) == len(nums):
            result.append(path[:])
            return
        for i in range(len(nums)):
            if used[i]:
                continue
            used[i] = True
            path.append(nums[i])
            backtrack()
            path.pop()
            used[i] = False

    backtrack()
    return result


print(permute([1, 2, 3]))
`);

  // ======================= JavaScript =======================
  add('js', 'js-list', '链表类与 for...of 迭代', `
class Node {
  constructor(value, next = null) {
    this.value = value;
    this.next = next;
  }
}

class LinkedList {
  constructor() {
    this.head = null;
    this.length = 0;
  }

  push(value) {
    const node = new Node(value);
    if (this.head === null) {
      this.head = node;
    } else {
      let cur = this.head;
      while (cur.next !== null) {
        cur = cur.next;
      }
      cur.next = node;
    }
    this.length++;
    return this;
  }

  removeFirst() {
    if (!this.head) return null;
    const old = this.head;
    this.head = old.next;
    this.length--;
    return old.value;
  }

  toArray() {
    const out = [];
    for (let cur = this.head; cur; cur = cur.next) out.push(cur.value);
    return out;
  }
}

const list = new LinkedList();
list.push("a").push("b").push("c");
console.log(list.removeFirst());
console.log(list.toArray(), list.length);
console.log(list);
`);

  add('js', 'js-tree', '二叉树：层序遍历与深度', `
class TreeNode {
  constructor(val, left = null, right = null) {
    this.val = val;
    this.left = left;
    this.right = right;
  }
}

function levelOrder(root) {
  const result = [];
  const queue = [root];
  while (queue.length > 0) {
    const level = [];
    const size = queue.length;
    for (let i = 0; i < size; i++) {
      const node = queue.shift();
      level.push(node.val);
      if (node.left) queue.push(node.left);
      if (node.right) queue.push(node.right);
    }
    result.push(level);
  }
  return result;
}

function maxDepth(node) {
  if (node === null) return 0;
  return 1 + Math.max(maxDepth(node.left), maxDepth(node.right));
}

const root = new TreeNode(3, new TreeNode(9), new TreeNode(20, new TreeNode(15), new TreeNode(7)));
console.log(levelOrder(root));
console.log("depth:", maxDepth(root));
`);

  add('js', 'js-map', 'Map / Set 与闭包计数器', `
function makeCounter() {
  let count = 0;            // 被闭包“记住”的变量
  return function () {
    count++;
    return count;
  };
}

const counter = makeCounter();
counter();
counter();
console.log("counter:", counter());

const words = ["apple", "bob", "apple", "cat", "bob", "apple"];
const freq = new Map();
for (const w of words) {
  freq.set(w, (freq.get(w) || 0) + 1);
}
const unique = new Set(words);
console.log(freq, unique.size);

const sorted = [...freq.entries()].sort((a, b) => b[1] - a[1]);
console.log(sorted[0]);
`);

  add('js', 'js-stack', '用数组实现栈：逆波兰表达式求值', `
function evalRPN(tokens) {
  const stack = [];
  for (const t of tokens) {
    if (["+", "-", "*", "/"].includes(t)) {
      const b = stack.pop();
      const a = stack.pop();
      if (t === "+") stack.push(a + b);
      else if (t === "-") stack.push(a - b);
      else if (t === "*") stack.push(a * b);
      else stack.push(Math.trunc(a / b));
    } else {
      stack.push(Number(t));
    }
  }
  return stack.pop();
}

console.log(evalRPN(["2", "1", "+", "3", "*"]));
console.log(evalRPN(["4", "13", "5", "/", "+"]));
`);

  // ======================= TypeScript =======================
  add('ts', 'ts-stack', '泛型栈与队列', `
class Stack<T> {
  private items: T[] = [];

  push(item: T): void {
    this.items.push(item);
  }

  pop(): T | undefined {
    return this.items.pop();
  }

  peek(): T | undefined {
    return this.items[this.items.length - 1];
  }

  get size(): number {
    return this.items.length;
  }
}

class Queue<T> {
  private items: T[] = [];
  enqueue(item: T): void { this.items.push(item); }
  dequeue(): T | undefined { return this.items.shift(); }
  isEmpty(): boolean { return this.items.length === 0; }
}

const s = new Stack<number>();
[1, 2, 3].forEach((n) => s.push(n));
console.log(s.pop(), s.peek(), s.size);

const q = new Queue<string>();
q.enqueue("x");
q.enqueue("y");
console.log(q.dequeue(), q.isEmpty());
`, { desc: '类型注解只在编译时检查，运行时会被去掉——所以可视化和 JavaScript 完全一样。' });

  add('ts', 'ts-list', '双向链表（interface + 类）', `
interface ListNode<T> {
  value: T;
  prev: ListNode<T> | null;
  next: ListNode<T> | null;
}

class DoublyLinkedList<T> {
  head: ListNode<T> | null = null;
  tail: ListNode<T> | null = null;

  append(value: T): void {
    const node: ListNode<T> = { value, prev: this.tail, next: null };
    if (this.tail) {
      this.tail.next = node;
    } else {
      this.head = node;
    }
    this.tail = node;
  }

  removeLast(): T | null {
    if (!this.tail) return null;
    const node = this.tail;
    this.tail = node.prev;
    if (this.tail) this.tail.next = null;
    else this.head = null;
    return node.value;
  }
}

const dll = new DoublyLinkedList<number>();
dll.append(1);
dll.append(2);
dll.append(3);
console.log(dll.removeLast());
`, { desc: 'prev 指针指向左边，所以会画成从下方绕回去的箭头。' });

  add('c', 'c-graph-bfs', '图的 BFS 与 DFS（邻接矩阵）', `
// 图的 BFS 与 DFS（邻接矩阵）
// graph[i][j] == 1 表示 i 和 j 之间有一条边（无向图）
// 右边会把邻接矩阵同时画成一张图；BFS 的队列和 visited 数组会一步步变化

#include <stdio.h>
#include <stdbool.h>

#define N 6

int graph[N][N];
bool visited[N];

void add_edge(int a, int b)
{
    graph[a][b] = 1;
    graph[b][a] = 1;
}

void bfs(int start)
{
    int queue[N];
    int head = 0, tail = 0;

    visited[start] = true;
    queue[tail++] = start;

    while (head < tail)
    {
        int u = queue[head++];      // 出队
        printf("%i ", u);
        for (int v = 0; v < N; v++)
        {
            if (graph[u][v] && !visited[v])
            {
                visited[v] = true;
                queue[tail++] = v;  // 入队
            }
        }
    }
    printf("\\n");
}

void dfs(int u)
{
    visited[u] = true;
    printf("%i ", u);
    for (int v = 0; v < N; v++)
    {
        if (graph[u][v] && !visited[v])
        {
            dfs(v);                 // 递归：调用栈就是 DFS 的“栈”
        }
    }
}

int main(void)
{
    add_edge(0, 1);
    add_edge(0, 2);
    add_edge(1, 3);
    add_edge(2, 4);
    add_edge(3, 5);
    add_edge(4, 5);

    printf("BFS: ");
    bfs(0);

    for (int i = 0; i < N; i++)
    {
        visited[i] = false;
    }

    printf("DFS: ");
    dfs(0);
    printf("\\n");
    return 0;
}
`, { desc: 'graph 是邻接矩阵，右侧会同时画成一张图。BFS 用数组 queue 和 head/tail 两个下标模拟队列；DFS 用递归，调用栈本身就是“栈”。' });

  add('c', 'c-inheritance', 'CS50 Inheritance：递归构建家谱树', `
// CS50 Inheritance：用递归构建三代家谱
// 每个人有两个 parents 指针，整体就是一棵“倒过来的”二叉树
// 注意看 create_family 递归时调用栈的变化，以及 free_family 按“后序”释放

#include <stdio.h>
#include <stdlib.h>

typedef struct person
{
    struct person *parents[2];
    char alleles[2];
}
person;

const int GENERATIONS = 3;

person *create_family(int generations);
void free_family(person *p);
char random_allele(void);

int main(void)
{
    srand(50);
    person *p = create_family(GENERATIONS);
    printf("Child blood type: %c%c\\n", p->alleles[0], p->alleles[1]);
    free_family(p);
    return 0;
}

person *create_family(int generations)
{
    person *new_person = malloc(sizeof(person));

    if (generations > 1)
    {
        // 先递归创建两位父母
        person *parent0 = create_family(generations - 1);
        person *parent1 = create_family(generations - 1);
        new_person->parents[0] = parent0;
        new_person->parents[1] = parent1;

        // 从每位父母随机继承一个等位基因
        new_person->alleles[0] = parent0->alleles[rand() % 2];
        new_person->alleles[1] = parent1->alleles[rand() % 2];
    }
    else
    {
        // 最老的一代：没有父母，等位基因随机
        new_person->parents[0] = NULL;
        new_person->parents[1] = NULL;
        new_person->alleles[0] = random_allele();
        new_person->alleles[1] = random_allele();
    }
    return new_person;
}

void free_family(person *p)
{
    if (p == NULL)
    {
        return;
    }
    // 先释放父母，再释放自己（后序遍历）
    free_family(p->parents[0]);
    free_family(p->parents[1]);
    free(p);
}

char random_allele(void)
{
    int r = rand() % 3;
    if (r == 0)
    {
        return 'A';
    }
    else if (r == 1)
    {
        return 'B';
    }
    else
    {
        return 'O';
    }
}
`, { desc: '每个 person 有 parents[2] 两个指针，三代人组成一棵二叉树。看 create_family 递归时调用栈一层层加深，以及 free_family 按后序释放。' });

  add('cpp', 'cpp-dijkstra', 'Dijkstra 最短路径（priority_queue）', `
// Dijkstra 最短路径（邻接表 + priority_queue）
// 看点：dist 数组被不断“松弛”，优先队列的堆顶永远是当前距离最小的点
#include <iostream>
#include <vector>
#include <queue>
using namespace std;

int main() {
    int n = 5;
    vector<vector<pair<int, int>>> adj(n);   // adj[u] = {(v, w), ...}
    adj[0].push_back({1, 4});
    adj[0].push_back({2, 1});
    adj[2].push_back({1, 2});
    adj[1].push_back({3, 1});
    adj[2].push_back({3, 5});
    adj[3].push_back({4, 3});

    const int INF = 1000000;
    vector<int> dist(n, INF);
    priority_queue<pair<int, int>, vector<pair<int, int>>, greater<pair<int, int>>> pq;

    dist[0] = 0;
    pq.push({0, 0});
    while (!pq.empty()) {
        auto [d, u] = pq.top();
        pq.pop();
        if (d > dist[u]) continue;           // 过期的记录
        for (auto [v, w] : adj[u]) {
            if (dist[u] + w < dist[v]) {     // 松弛
                dist[v] = dist[u] + w;
                pq.push({dist[v], v});
            }
        }
    }
    for (int i = 0; i < n; i++) cout << "dist[" << i << "] = " << dist[i] << endl;
    return 0;
}
`, { desc: 'adj 是邻接表（vector 套 vector）。pq 是小顶堆：堆顶永远是当前距离最小的点；dist 被一次次松弛变小。' });

  add('java', 'java-graph', '图的 DFS 与 BFS（邻接表）', `
// 图的 DFS / BFS（邻接表：List<List<Integer>>）
// 看点：递归 DFS 的调用栈，和 BFS 里 Queue 的入队、出队
import java.util.*;

public class Main {
    static List<List<Integer>> adj = new ArrayList<>();
    static boolean[] visited;

    static void addEdge(int a, int b) {
        adj.get(a).add(b);
        adj.get(b).add(a);
    }

    static void dfs(int u, List<Integer> order) {
        visited[u] = true;
        order.add(u);
        for (int v : adj.get(u)) {
            if (!visited[v]) {
                dfs(v, order);
            }
        }
    }

    static List<Integer> bfs(int start) {
        List<Integer> order = new ArrayList<>();
        boolean[] seen = new boolean[adj.size()];
        Queue<Integer> queue = new LinkedList<>();
        queue.offer(start);
        seen[start] = true;
        while (!queue.isEmpty()) {
            int u = queue.poll();
            order.add(u);
            for (int v : adj.get(u)) {
                if (!seen[v]) {
                    seen[v] = true;
                    queue.offer(v);
                }
            }
        }
        return order;
    }

    public static void main(String[] args) {
        int n = 5;
        for (int i = 0; i < n; i++) adj.add(new ArrayList<>());
        addEdge(0, 1);
        addEdge(0, 2);
        addEdge(1, 3);
        addEdge(2, 3);
        addEdge(3, 4);

        visited = new boolean[n];
        List<Integer> order = new ArrayList<>();
        dfs(0, order);
        System.out.println("DFS: " + order);
        System.out.println("BFS: " + bfs(0));
    }
}
`, { desc: 'adj 是 List<List<Integer>>：每个点一个邻居列表。DFS 看调用栈，BFS 看 Queue 的入队与出队。' });

  add('python', 'py-dijkstra', 'Dijkstra 最短路径（heapq）', `
# Dijkstra 最短路径（邻接表 + heapq 小顶堆）
# 看点：dist 字典怎样被一步步“松弛”变小，堆顶总是当前最近的点
import heapq

graph = {
    "A": [("B", 4), ("C", 1)],
    "B": [("D", 1)],
    "C": [("B", 2), ("D", 5)],
    "D": [("E", 3)],
    "E": [],
}

def dijkstra(graph, start):
    dist = {node: float("inf") for node in graph}
    dist[start] = 0
    prev = {}
    heap = [(0, start)]
    while heap:
        d, u = heapq.heappop(heap)
        if d > dist[u]:
            continue          # 旧的记录，已经有更短的路了
        for v, w in graph[u]:
            nd = d + w
            if nd < dist[v]:  # 松弛
                dist[v] = nd
                prev[v] = u
                heapq.heappush(heap, (nd, v))
    return dist, prev

dist, prev = dijkstra(graph, "A")
print(dist)

# 沿着 prev 反推路径
path = []
node = "E"
while node != "A":
    path.append(node)
    node = prev[node]
path.append("A")
print(" -> ".join(reversed(path)))
`, { desc: 'graph 是“字典 + 列表”的邻接表。看 dist 怎样被松弛、heap 堆顶怎样变化，最后沿 prev 反推出路径。' });

  add('python', 'py-unionfind', '并查集：路径压缩 + 按大小合并', `
# 并查集（Union-Find）：路径压缩 + 按大小合并
# parent[i] 指向 i 的“上级”，一直往上找就能找到所在集合的代表（根）

class UnionFind:
    def __init__(self, n):
        self.parent = list(range(n))
        self.size = [1] * n

    def find(self, x):
        if self.parent[x] != x:
            self.parent[x] = self.find(self.parent[x])  # 路径压缩
        return self.parent[x]

    def union(self, a, b):
        ra, rb = self.find(a), self.find(b)
        if ra == rb:
            return False
        if self.size[ra] < self.size[rb]:
            ra, rb = rb, ra
        self.parent[rb] = ra        # 小树挂到大树下面
        self.size[ra] += self.size[rb]
        return True

uf = UnionFind(6)
edges = [(0, 1), (2, 3), (1, 3), (4, 5), (0, 2)]
for a, b in edges:
    merged = uf.union(a, b)
    print(a, b, "合并" if merged else "已连通（这条边会成环）")

groups = {}
for i in range(6):
    groups.setdefault(uf.find(i), []).append(i)
print(list(groups.values()))
`, { desc: 'parent 列表里每个位置指向自己的“上级”。find 递归时会把沿途的点直接挂到根上（路径压缩）。' });

  add('python', 'py-islands', '岛屿数量：网格上的 DFS', `
# 岛屿数量：在二维网格上做 DFS（洪水填充）
# grid 是“列表的列表”；每找到一块新陆地，就把整座岛标记成已访问

grid = [
    ["1", "1", "0", "0"],
    ["1", "0", "0", "1"],
    ["0", "0", "1", "1"],
    ["0", "0", "0", "1"],
]

def num_islands(grid):
    rows, cols = len(grid), len(grid[0])
    count = 0

    def dfs(r, c):
        if r < 0 or r >= rows or c < 0 or c >= cols or grid[r][c] != "1":
            return
        grid[r][c] = "#"        # 标记为已访问
        dfs(r + 1, c)
        dfs(r - 1, c)
        dfs(r, c + 1)
        dfs(r, c - 1)

    for r in range(rows):
        for c in range(cols):
            if grid[r][c] == "1":
                count += 1
                dfs(r, c)
    return count

print(num_islands(grid))
`, { desc: 'grid 是列表的列表。每次发现新陆地就递归 DFS，把整座岛标成 #；调用栈最深时能看到四个方向的搜索顺序。' });

  add('js', 'js-topo', '拓扑排序（Kahn 算法）', `
// 拓扑排序（Kahn 算法）：课程先修关系
// 入度为 0 的课可以先上；上完之后，把它指向的课的入度减 1
const courses = ["C 语言", "数据结构", "算法", "操作系统", "编译原理"];
const prereq = [
  [0, 1], // C 语言 -> 数据结构
  [1, 2], // 数据结构 -> 算法
  [0, 3], // C 语言 -> 操作系统
  [2, 4], // 算法 -> 编译原理
  [3, 4], // 操作系统 -> 编译原理
];

function topoSort(n, edges) {
  const adj = Array.from({ length: n }, () => []);
  const indegree = new Array(n).fill(0);
  for (const [a, b] of edges) {
    adj[a].push(b);
    indegree[b]++;
  }
  const queue = [];
  for (let i = 0; i < n; i++) if (indegree[i] === 0) queue.push(i);

  const order = [];
  while (queue.length > 0) {
    const u = queue.shift();
    order.push(u);
    for (const v of adj[u]) {
      indegree[v]--;
      if (indegree[v] === 0) queue.push(v);
    }
  }
  return order.length === n ? order : null; // null 说明有环
}

const order = topoSort(courses.length, prereq);
console.log(order.map(i => courses[i]).join(" → "));
`, { desc: 'indegree 记录每门课还差几门先修课。入度为 0 的课进入 queue；出队一门，就把它指向的课入度减 1。' });

  add('python', 'py-hof', '高阶函数：make_adder 与 compose', `
# 高阶函数与环境图（CS61A 风格）
# 看点：每次调用都会新建一个帧 f1、f2…，它的 parent 是“函数被定义时所在的帧”，
# 而不是调用它的地方。查找变量时，先找当前帧，找不到就沿着 parent 往上找。

def make_adder(n):
    def adder(k):
        return k + n        # n 不在 adder 的帧里，要去 parent（make_adder 的帧）找
    return adder

def compose1(f, g):
    def h(x):
        return f(g(x))
    return h

square = lambda x: x * x
add_three = make_adder(3)
f = compose1(square, add_three)
result = f(2)
print(result)
`, { desc: '左边的每个帧都标着 f1: 函数名 [parent=…]。函数被画成对象，它的 parent 是定义它时所在的帧。已经返回的帧会变灰但保留，方便对照 CS61A 的环境图。' });

  add('python', 'py-closure', '闭包与 nonlocal：计数器', `
# 闭包与 nonlocal：计数器
# make_counter 返回之后，它的帧并没有消失——counter 的 parent 还指着它，
# 所以 count 一直“活着”。两个计数器各有自己的帧，互不影响。

def make_counter():
    count = 0
    def counter():
        nonlocal count      # 修改的是 parent 帧里的 count
        count += 1
        return count
    return counter

a = make_counter()
b = make_counter()
a()
a()
b()
print(a(), b())
`, { desc: 'make_counter 返回后，它的帧仍被 counter 的 parent 引用，所以 count 一直存在。a 和 b 是两个独立的闭包，各自指向不同的帧。' });

  add('python', 'py-curry', '柯里化与 apply_twice', `
# 柯里化与函数作为参数（CS61A Lecture 5 风格）

def curry2(f):
    def g(x):
        def h(y):
            return f(x, y)
        return h
    return g

def apply_twice(f, x):
    return f(f(x))

from operator import add, mul

add_curried = curry2(add)
add_five = add_curried(5)
print(add_five(10))
print(apply_twice(add_five, 1))
print(curry2(mul)(3)(4))
`, { desc: '函数可以当参数传、当返回值。注意 curry2 里三层嵌套：h 的 parent 是 g 的帧，g 的 parent 是 curry2 的帧，查找 f、x 时会一层层往上找。' });

  add('js', 'js-closure', '闭包与高阶函数：makeAdder / compose / 计数器', `
// 闭包与高阶函数（环境图）
// 每次调用新建一个帧 f1、f2…；函数对象记住“创建它时所在的帧”（parent）。
// 找变量时：当前帧 → parent → parent 的 parent … → Global

function makeAdder(n) {
  return function adder(k) {
    return k + n;          // n 来自 parent 帧（makeAdder 的帧）
  };
}

const compose = (f, g) => x => f(g(x));
const square = x => x * x;

const addThree = makeAdder(3);
const h = compose(square, addThree);
console.log(h(2));

function makeCounter() {
  let count = 0;
  return () => {
    count += 1;            // 修改的是 makeCounter 帧里的 count
    return count;
  };
}

const a = makeCounter();
const b = makeCounter();
a();
a();
console.log(a(), b());
`, { desc: '帧标题写着 f1: 函数名 [parent=…]，函数画成对象并标出 parent。makeCounter 返回后它的帧仍然保留（变灰），因为返回的箭头函数还在用里面的 count。' });

  // 分类（下拉框里按组显示）
  const CAT = {
    'py-hof': '高阶函数 · 环境图', 'py-closure': '高阶函数 · 环境图', 'py-curry': '高阶函数 · 环境图', 'js-closure': '高阶函数 · 环境图',
    'c-tideman': '图', 'c-graph-bfs': '图', 'cpp-graph': '图', 'cpp-dijkstra': '图', 'java-graph': '图', 'py-bfs': '图', 'py-dijkstra': '图', 'py-unionfind': '图', 'py-islands': '图', 'js-topo': '图',
    'c-bst': '树', 'c-trie': '树', 'c-inheritance': '树', 'cpp-bst': '树', 'java-bst': '树', 'py-bst': '树', 'js-tree': '树',
    'c-list-argv': '链表', 'c-list-ops': '链表', 'cpp-list': '链表', 'java-list': '链表', 'py-list': '链表', 'js-list': '链表', 'ts-list': '链表',
    'c-stack-queue': '栈 · 队列 · 堆', 'java-stack-queue': '栈 · 队列 · 堆', 'java-heap': '栈 · 队列 · 堆', 'py-heap': '栈 · 队列 · 堆', 'js-stack': '栈 · 队列 · 堆', 'ts-stack': '栈 · 队列 · 堆', 'cpp-stl': '栈 · 队列 · 堆',
    'c-hash': '哈希表 · 字典', 'java-hashmap': '哈希表 · 字典', 'py-dict': '哈希表 · 字典', 'js-map': '哈希表 · 字典',
    'c-sort': '排序 · 递归', 'c-recursion': '排序 · 递归', 'py-sort': '排序 · 递归', 'py-recursion': '排序 · 递归',
  };
  DSV.exCats = ['高阶函数 · 环境图', '图', '树', '链表', '栈 · 队列 · 堆', '哈希表 · 字典', '排序 · 递归', '基础'];
  for (const e of E) e.cat = CAT[e.id] || '基础';

  DSV.examples = E;
  DSV.blankCode = {
    c: '#include <stdio.h>\n\nint main(void)\n{\n    printf("hello, world\\n");\n}\n',
    cpp: '#include <iostream>\nusing namespace std;\n\nint main() {\n    cout << "hello, world" << endl;\n}\n',
    java: 'public class Main {\n    public static void main(String[] args) {\n        System.out.println("hello, world");\n    }\n}\n',
    python: 'print("hello, world")\n',
    js: 'console.log("hello, world");\n',
    ts: 'const greeting: string = "hello, world";\nconsole.log(greeting);\n',
  };
})(typeof window !== 'undefined' ? window : globalThis);
