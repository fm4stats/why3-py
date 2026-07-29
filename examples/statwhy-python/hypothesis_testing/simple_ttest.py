# translated from the first part of examples/mlw/ex_ttest.mlw.

from statwhy import string, NormalD, Param, real, exec_ttest_1samp, Two, dataset, Interval
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

#@ execution

d1 = dataset(data=[
    -0.03535040960569304,
    -0.15843246053760296,
    0.8242427720812421,
    -0.42823268167163975,
    0.19617481535793227,
    -0.2707760280674015,
    -1.031181612039124,
    -1.1956445956869606,
    0.09750947857185115,
    -1.1600796427840516
], scale=Interval)

print("p-value of ex_ttest_1samp(d1): %f" % ex_ttest_1samp(d1))

# % ./env-why3 python3 ./examples/statwhy-python/hypothesis_testing/simple_ttest.py
# p-value of ex_ttest_1samp(d1): 0.160664
