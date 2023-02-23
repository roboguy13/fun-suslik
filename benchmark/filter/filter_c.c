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

// manual
loc f(int len)
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

void filter(loc y, loc ret)
{
    loc y01 = READ_LOC(y, 0);
    loc a1 = READ_LOC(ret, 0);
    if ((y01 == 0))
    {
        WRITE_INT(ret, 0, 0);
        return;
    }
    else
    {
        loc vy011 = READ_LOC(y01, 0);
        loc nxty011 = READ_LOC(y01, 1);
        if ((vy011 < 9))
        {
            WRITE_LOC(y, 0, nxty011);
            filter(y, ret);
            loc ret011 = READ_LOC(ret, 0);
            WRITE_LOC(y, 0, y01);
            return;
        }
        else
        {
            WRITE_LOC(y, 0, nxty011);
            filter(y, ret);
            loc ret011 = READ_LOC(ret, 0);
            loc ret02 = (loc)malloc(2 * sizeof(loc));
            WRITE_LOC(ret, 0, ret02);
            WRITE_LOC(y, 0, y01);
            WRITE_LOC(ret02, 1, ret011);
            WRITE_LOC(ret02, 0, vy011);
            return;
        }
    }
}
int main()
{
    loc l1 = f(50000);
    // loc l2 = f(100000);
    loc in1 = malloc(sizeof(loc));
    WRITE_LOC(in1, 0, l1);
    // loc in2 = malloc(sizeof(loc));
    // WRITE_LOC(in2, 0, l2);
    clock_t start_t, end_t;
    start_t = clock();
    loc output = malloc(sizeof(loc));
    filter(in1, output);
    end_t = clock();
    double total_t = (double)(end_t - start_t) / CLOCKS_PER_SEC;
    printf("Total time taken by CPU: %f sec\n", total_t);
    return 0;
}
