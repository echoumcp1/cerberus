int live_RW_footprint(char *p, char *q)
/*@
 requires
    take P = RW<int[11]>(array_shift<char>(p, -2i64));
    ptr_eq(q, array_shift<char>(p, 12i64));
ensures
    take P2 = RW<int[11]>(array_shift<char>(p, -2i64));
    P == P2;
    return == 12i32;
@*/
{
  /*@ focus RW<int>, 7u64; @*/
  // NOTE: neither argument needs to be in the footprint of the RW
  // The bounds check for the allocation are done separately to the resource
  // lookup
  return q - p;
}

// Here, only one ownership is required to establish the that the allocation is
// live, but both are required to ensure that the bounds check succeeds
int live_RW_both(int *p, int *q)
/*@
 requires
    take P = RW(p);
    take Q = RW(q);
    ptr_eq(q, array_shift(p, 10i32));
ensures
    take P2 = RW(p);
    P == P2;
    take Q2 = RW(q);
    Q == Q2;
    return == -10i32;
@*/
{
  return p - q;
}

int live_RW_one(int *p, int *q)
/*@
 requires
    take P = RW(p);
    ptr_eq(q, array_shift(p, 10i32));
    let A = allocs[(alloc_id)p];
    (u64) p <= (u64) q;
    (u64) q <= A.base + A.size;
ensures
    take P2 = RW(p);
    P == P2;
    return == -10i32;
@*/
{
  return p - q;
}

int live_alloc(int *p, int *q)
/*@
 requires
    !is_null(p);
    ptr_eq(q, array_shift(p, 10i32));
    take A = Alloc(p);
    A.base <= (u64) p;
    (u64) p <= (u64) q;
    (u64) q <= A.base + A.size;
ensures
    return == -10i32;
    take A2 = Alloc(p);
    A == A2;
@*/
{
  /*@ assert(allocs[(alloc_id)p] == A); @*/
  return p - q;
}

int main(void)
{
    int arr[11] = { 0 };
    live_alloc(&arr[0], &arr[10]);
    /*@ focus RW<int>, 0u64; @*/
    /*@ focus RW<int>, 10u64; @*/
    live_RW_one(&arr[0], &arr[10]);
    live_RW_both(&arr[0], &arr[10]);
    char *p = (char*) arr;
    live_RW_footprint(p + 2, p + 14);
}
