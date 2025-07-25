def reverse(a):
    #@ requires len(a) > 0
    #@ ensures len(result) = len(old(a))
    #@ ensures len(a) = 0
    #@ ensures forall i. 0 <= i < len(result) -> result[i] = (old(a))[-(i+1)]
    #@ label L

    res = []

    while(len(a) != 0):
        #@ invariant len(a) + len(res) = len(a) at L
        #@ invariant forall i. 0 <= i < len(res) -> res[i] = a[-(i+1)] at L
        #@ invariant forall i. 0 <= i < len(a) -> a[i] = a[i] at L
        #@ variant len(a)
        res.append(a.pop())

    return res
