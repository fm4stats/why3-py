# translated from the first part of examples/mlw/ex_ftest.mlw.

from statwhy import string, NormalD, Param, real, Two, dataset, Interval
from statwhy import exec_ftest
#@ use cameleerBHL.CameleerBHL
#@ use ftest.Ftest

m1 = "mean1"
m2 = "mean2"
v1 = "var1"
v2 = "var2"

p1 = NormalD(Param(m1), Param(v1))
p2 = NormalD(Param(m2), Param(v1))

def ex_ftest2(d1, d2) -> real:
    #@ requires \
    #@    is_empty !st /\ \
    #@    sampled d1 p1 /\ sampled d2 p2 /\ \
    #@    independent d1 d2 /\ \
    #@    d1.scale = d2.scale = Interval /\ \
    #@    (World !st interp) |= Possible (var p1 $< var p2) /\ \
    #@    (World !st interp) |= Possible (var p1 $> var p2)
    #@ ensures \
    #@    let p = result in \
    #@    Eq p = compose_pvs (var p1 $!= var p2) !st && \
    #@    (World !st interp) |= StatB (Eq p) (var p1 $!= var p2)
    return exec_ftest(p1, p2, d1, d2, Two)

#@ execution

d1 = dataset(data=[1.01, 1.03, 1.02, 1.04], scale=Interval)
d2 = dataset(data=[2.00, 2.03, 2.01, 2.05], scale=Interval)

print("p-value: %f" % ex_ftest2(d1, d2))
