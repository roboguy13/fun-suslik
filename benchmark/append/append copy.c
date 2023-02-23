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

void sll_copy(loc x0, loc y)
{
    loc a1 = READ_LOC(y, 0);
    if ((x0 == NULL))
    {
        WRITE_INT(y, 0, 0);
        return;
    }
    else
    {
        loc vx01 = READ_LOC(x0, 0);
        loc nxtx01 = READ_LOC(x0, 1);
        sll_copy(nxtx01, y);
        loc y011 = READ_LOC(y, 0);
        loc y02 = (loc)malloc(2 * sizeof(loc));
        WRITE_LOC(y, 0, y02);
        WRITE_LOC(y02, 1, y011);
        WRITE_LOC(y02, 0, vx01);
        return;
    }
}

void cons(loc v, loc x, loc y)
{
    loc x01 = READ_LOC(x, 0);
    loc a1 = READ_LOC(y, 0);
    int vv1 = READ_INT(v, 0);
    loc y01 = (loc)malloc(2 * sizeof(loc));
    WRITE_LOC(y, 0, y01);
    WRITE_INT(y01, 0, vv1);
    // sll_copy(x01, (y01 + 1));
    WRITE_LOC(y01, 1, x01);
    return;
}

void append(loc x, loc y, loc ret)
{
    loc x01 = READ_LOC(x, 0);
    loc y01 = READ_LOC(y, 0);
    loc a1 = READ_LOC(ret, 0);
    if ((x01 == NULL))
    {
        // sll_copy(y01, ret);
        WRITE_LOC(ret, 0, y01);
        return;
    }
    else
    {
        loc vx011 = READ_LOC(x01, 0);
        loc nxtx011 = READ_LOC(x01, 1);
        loc tx011 = (loc)malloc(1 * sizeof(loc));
        WRITE_LOC(ret, 0, nxtx011);
        append(ret, y, tx011);
        cons(x01, tx011, ret);
        // typefree(tx011, tx0111);
        return;
    }
}

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
int main()
{
    // loc l1 = (loc)malloc(2 * sizeof(loc));
    // WRITE_LOC(l1, 0, 1);
    // loc l2 = (loc)malloc(2 * sizeof(loc));
    // WRITE_LOC(l1, 1, l2);
    // WRITE_LOC(l2, 0, 2);
    // WRITE_LOC(l2, 1, 0);
    // print_sll(l1);
    // loc output = malloc(sizeof(loc));
    // // sll_copy(l1, output);
    // // loc output0 = output->ssl_ptr;
    // // print_sll(output0);

    // loc in1 = malloc(sizeof(loc));
    // WRITE_LOC(in1, 0, l1);
    // loc in2 = malloc(sizeof(loc));
    // sll_copy(l1, in2);
    // print_sll(in2->ssl_ptr);
    // loc v = (loc)malloc(sizeof(loc));
    // WRITE_INT(v, 0, 3);
    // append(in1, in2, output);
    // loc output0 = output->ssl_ptr;
    // print_sll(output0);


    loc l1 = f(100000);
    loc l2 = f(100000);
    loc in1 = malloc(sizeof(loc));
    WRITE_LOC(in1, 0, l1);
    loc in2 = malloc(sizeof(loc));
    WRITE_LOC(in2, 0, l2);
    clock_t start_t, end_t;
    start_t = clock();
    loc output = malloc(sizeof(loc));
    append(in1, in2, output);
    end_t = clock();
    double total_t = (double)(end_t - start_t) / CLOCKS_PER_SEC;
    printf("Total time taken by CPU: %f\n", total_t  );
    return 0;
}
