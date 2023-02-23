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

void print_multi(loc x)
{
    if ((x == NULL))
    {
        printf("Empty\n");
    }
    else
    {
        loc l = (loc)(READ_LOC(x, 0));
        printf("sublist:");
        loc next = (loc)READ_LOC(x, 1);
        print_sll(l);
        print_multi(next);
    }
    return;
}

void print_sll(loc x)
{
    if ((x == NULL))
    {
        printf("Nil\n");
    }
    else
    {
        int num = (int)(READ_LOC(x, 0));
        printf("%d, ", num);
        loc next = (loc)READ_LOC(x, 1);
        print_sll(next);
    }
    return;
}

loc sll_range(int len)
{
    assert(len > 0);
    loc init = (loc)malloc(2 * sizeof(loc));
    loc run = init;
    for (int i = 1; i <= len; ++i)
    {
        loc tmp = (loc)malloc(2 * sizeof(loc));
        WRITE_LOC(run, 0, i);
        if (i < len)
        {
            WRITE_LOC(run, 1, tmp);
            run = tmp;
        }
        else
        {
            WRITE_LOC(run, 1, 0);
        }
    }
    return init;
}

loc multilist_range(int x, int y)
{
    loc init = (loc)malloc(2 * sizeof(loc));
    loc run = init;

    for (int i = 1; i <= x; ++i)
    {
        loc tmp = (loc)malloc(2 * sizeof(loc));
        loc subl = sll_range(y);
        WRITE_LOC(run, 0, subl);
        if (i < x)
        {
            WRITE_LOC(run, 1, tmp);
            run = tmp;
        }
        else
        {
            WRITE_LOC(run, 1, 0);
        }
    }
    return init;
}

void map_sum(loc x, loc y)
{
    loc x01 = READ_LOC(x, 0);
    loc a1 = READ_LOC(y, 0);
    if ((x01 == 0))
    {
        WRITE_INT(y, 0, 0);
        return;
    }
    else
    {
        loc hx011 = READ_LOC(x01, 0);
        loc xnxtx011 = READ_LOC(x01, 1);
        WRITE_LOC(x, 0, xnxtx011);
        map_sum(x, y);
        loc y011 = READ_LOC(y, 0);
        loc y02 = (loc)malloc(2 * sizeof(loc));
        WRITE_LOC(y, 0, y02);
        WRITE_LOC(x, 0, x01);
        WRITE_LOC(y02, 1, y011);
        sum(x01, y02);
        return;
    }
}

void sum(loc x, loc ret)
{
    loc x01 = READ_LOC(x, 0);
    loc a1 = READ_LOC(ret, 0);
    if ((x01 == 0))
    {
        WRITE_INT(ret, 0, 0);
        return;
    }
    else
    {
        loc vx011 = READ_LOC(x01, 0);
        loc nxtx011 = READ_LOC(x01, 1);
        WRITE_LOC(x, 0, nxtx011);
        sum(x, ret);
        int ret011 = READ_INT(ret, 0);
        WRITE_LOC(x, 0, x01);
        WRITE_INT(ret, 0, ((int)ret011 + (int)vx011));
        return;
    }
}

int main()
{
    loc l1 = multilist_range(1000, 1000);
    loc in1 = malloc(sizeof(loc));
    WRITE_LOC(in1, 0, l1);
    clock_t start_t, end_t;
    start_t = clock();
    loc output = malloc(sizeof(loc));
    map_sum(in1, output);
    end_t = clock();
    double total_t = (double)(end_t - start_t) / CLOCKS_PER_SEC;
    printf("Total time taken by CPU: %f sec\n", total_t);
    return 0;
}
