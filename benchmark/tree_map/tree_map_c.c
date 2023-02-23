#include <stddef.h>
#include <stdio.h>
#include <assert.h>
#include <time.h>
#include <stdint.h>

extern void free(void *p);
extern void *malloc(size_t size);

typedef union sslval
{
    int ssl_int;
    void *ssl_ptr;
} *loc;
#define READ_LOC(x, y) (*(x + y)).ssl_ptr
#define READ_INT(x, y) (*(x + y)).ssl_int
#define WRITE_LOC(x, y, z) (*(x + y)).ssl_ptr = z
#define WRITE_INT(x, y, z) (*(x + y)).ssl_int = z

void print_tree(loc x)
{
    if ((x == NULL))
    {
        printf("Empty\n");
    }
    else
    {
        int num = (int)(READ_LOC(x, 0));
        printf("%d then\n", num);
        loc l = (loc)READ_LOC(x, 1);
        loc r = (loc)READ_LOC(x, 2);
        print_tree(l);
        print_tree(r);
    }
    return;
}

// manual
loc tree_range(int i, int len)
{
    if (len < i)
    {
        return NULL;
    }
    loc init = (loc)malloc(3 * sizeof(loc));
    WRITE_LOC(init, 0, i);
    loc l = tree_range(i + 1, len);
    loc r = tree_range(i + 1, len);
    WRITE_LOC(init, 1, l);
    WRITE_LOC(init, 2, r);
    return init;
}

void sll_plus1(loc x, loc y)
{
    loc x01 = READ_LOC(x, 0);
    loc a1 = READ_LOC(y, 0);
    if ((x01 == NULL))
    {
        WRITE_INT(y, 0, 0);
        return;
    }
    else
    {
        int vx011 = READ_INT(x01, 0);
        loc nxtx011 = READ_LOC(x01, 1);
        WRITE_LOC(x, 0, nxtx011);
        sll_plus1(x, y);
        loc y011 = READ_LOC(y, 0);
        loc y02 = (loc)malloc(2 * sizeof(loc));
        WRITE_LOC(y, 0, y02);
        WRITE_LOC(x, 0, x01);
        WRITE_LOC(y02, 1, y011);
        WRITE_INT(y02, 0, (vx011 + 1));
        return;
    }
}

void tree_plus1(loc x, loc y)
{
    loc x01 = READ_LOC(x, 0);
    loc a1 = READ_LOC(y, 0);
    if ((x01 == NULL))
    {
        WRITE_LOC(y, 0, 0);//todo fix
        return;
    }
    else
    {
        int vx011 = READ_INT(x01, 0); //todo fix
        loc lx011 = READ_LOC(x01, 1);
        loc rx011 = READ_LOC(x01, 2);
        WRITE_LOC(x, 0, lx011);
        tree_plus1(x, y);
        loc y011 = READ_LOC(y, 0);
        WRITE_LOC(x, 0, rx011);
        tree_plus1(x, y);
        loc y021 = READ_LOC(y, 0);
        loc y03 = (loc)malloc(3 * sizeof(loc));
        WRITE_LOC(y, 0, y03);
        WRITE_LOC(x, 0, x01);
        WRITE_LOC(y03, 1, y011);
        WRITE_LOC(y03, 2, y021);
        WRITE_INT(y03, 0, ((int)vx011 + 1));
        return;
    }
}
int main()
{
    loc l1 = tree_range(1, 20);
    // print_tree(l1);
    loc in1 = malloc(sizeof(loc));
    WRITE_LOC(in1, 0, l1);
    clock_t start_t, end_t;
    start_t = clock();
    loc output = malloc(sizeof(loc));
    tree_plus1(in1, output);
    end_t = clock();
    double total_t = (double)(end_t - start_t) / CLOCKS_PER_SEC;
    printf("Total time taken by CPU: %f sec\n", total_t);
    return 0;
}
