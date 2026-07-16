# translated from the first part of examples/mlw/ex_binom.mlw.

from statwhy import string, real, Two, dataset
from statwhy import Nil, Cons, Param, CategoricalD, Nominal
from statwhy import exec_binom_test
#@ use cameleerBHL.CameleerBHL
#@ use binom.Binom

bp = CategoricalD(Cons(Param("p1"), Nil))

def ex_binom_Two(p0, d) -> real:
    #@ requires \
    #@    is_empty !st /\ \
    #@    is_binary_dataset d /\ \
    #@    d.scale = Nominal /\ \
    #@    (World !st interp) |= Possible (bernoullip bp $< const_term p0) /\ \
    #@    (World !st interp) |= Possible (bernoullip bp $> const_term p0)

    #@ ensures \
    #@    let pv = result in \
    #@    (Eq pv) = compose_pvs (bernoullip bp $!= const_term p0) !st && \
    #@    (World !st interp) |= StatB (Eq pv) (bernoullip bp $!= const_term p0)
    return exec_binom_test(bp, p0, d, Two)

#@ execution

d = dataset(data=[1, 1, 1, 1, 1, 1, 1, 0, 0, 0], scale=Nominal)

print("p-value: %f" % ex_binom_Two(0.5, d))
