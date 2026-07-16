# translated from the first part of examples/mlw/ex_bartlett.mlw.

from statwhy import Nil, Cons, string, NormalD, Param, real, Two, dataset, Interval
from statwhy import exec_bartlett
#@ use cameleerBHL.CameleerBHL
#@ use bartlett.Bartlett

m1 = "mean1"
m2 = "mean2"
m3 = "mean3"
v1 = "var1"
v2 = "var2"
v3 = "var3"

p1 = NormalD(Param(m1), Param(v1))
p2 = NormalD(Param(m2), Param(v2))
p3 = NormalD(Param(m3), Param(v3))

def ex_bartlett3(d1, d2, d3) -> real:
    #@ requires \
    #@    is_empty !st /\ \
    #@    sampled d1 p1 /\ sampled d2 p2 /\ sampled d3 p3 /\ \
    #@    independent_list (Cons d1 (Cons d2 (Cons d3 Nil))) /\ \
    #@    d1.scale = d2.scale = d3.scale = Interval /\ \
    #@    (World !st interp) |= Possible (var p1 $< var p2) /\ \
    #@    (World !st interp) |= Possible (var p1 $< var p3) /\ \
    #@    (World !st interp) |= Possible (var p2 $< var p3) /\ \
    #@    (World !st interp) |= Possible (var p1 $> var p2) /\ \
    #@    (World !st interp) |= Possible (var p1 $> var p3) /\ \
    #@    (World !st interp) |= Possible (var p2 $> var p3)
    #@ ensures \
    #@    let p = result in \
    #@    let h = (var p1 $!= var p2) $|| (var p1 $!= var p3) $|| (var p2 $!= var p3) in \
    #@    Eq p = compose_pvs h !st && \
    #@    (World !st interp) |= StatB (Eq p) h
    return exec_bartlett(Cons(p1, Cons(p2, Cons(p3, Nil))), \
                         Cons(d1, Cons(d2, Cons(d3, Nil))))

#@ execution

d1 = dataset(data=[1.01, 1.03, 1.02, 1.04], scale=Interval)
d2 = dataset(data=[2.00, 2.03, 2.01, 2.05], scale=Interval)
d3 = dataset(data=[2.01, 2.02, 2.01, 2.05], scale=Interval)

print("p-value: %f" % ex_bartlett3(d1, d2, d3))
