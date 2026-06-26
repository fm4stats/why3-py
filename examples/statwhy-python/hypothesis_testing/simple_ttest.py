# translated from the first part of examples/mlw/ex_ttest.mlw.

from statwhy import string, NormalD, Param, real, exec_ttest_1samp, Two
#@ use cameleerBHL.CameleerBHL
#@ use ttest.Ttest

m = "mean1"
v = "var1"
pp = NormalD(Param(m), Param(v))

def ex_ttest_1samp(d) -> real :
    #@ requires \
    #@    d.scale = Interval /\ \
    #@    is_empty !st /\ \
    #@    sampled d pp /\ \
    #@    (World !st interp) |= Possible (mean pp $< const_term 0.0) /\ \
    #@    (World !st interp) |= Possible (mean pp $> const_term 0.0)
    #@ ensures \
    #@    let p = result in \
    #@    Eq p = compose_pvs (mean pp $!= const_term 0.0) !st && \
    #@    (World !st interp) |= StatB (Eq p) (mean pp $!= const_term 0.0)
    return exec_ttest_1samp(pp, 0.0, d, Two)
