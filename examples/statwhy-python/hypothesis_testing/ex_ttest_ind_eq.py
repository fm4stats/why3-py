# translated from part of examples/mlw/ex_ttest.mlw.

from statwhy import string, NormalD, Param, real, Two, dataset, Interval
from statwhy import exec_ttest_ind_eq
#@ use cameleerBHL.CameleerBHL
#@ use ttest.Ttest

m1 = "mean1"
v1 = "var1"
pp1 = NormalD(Param(m1), Param(v1))

m2 = "mean2"
v2 = "var2"
pp2 = NormalD(Param(m2), Param(v2))

def ex_ttest_ind_eq(d1, d2) -> real :
    #@ requires \
    #@    d1.scale = d2.scale = Interval /\ \
    #@    independent d1 d2 /\ \
    #@    is_empty !st /\ \
    #@    sampled d1 pp1 /\ sampled d2 pp2 /\ \
    #@    (World !st interp) |= Know (var pp1 $= var pp2) /\ \
    #@    (World !st interp) |= eq_variance pp1 pp2 /\ \
    #@    (World !st interp) |= Possible (mean pp1 $< mean pp2) /\ \
    #@    (World !st interp) |= Possible (mean pp1 $> mean pp2)

    #@ ensures \
    #@    let p = result in \
    #@    Eq p = compose_pvs (mean pp1 $!= mean pp2) !st && \
    #@    (World !st interp) |= StatB (Eq p) (mean pp1 $!= mean pp2)
    return exec_ttest_ind_eq(pp1, pp2, d1, d2, Two)

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

d2 = dataset(data=[
    -0.9275157194364511,
    -0.4244748203039643,
    -1.1723303937287286,
    0.3775047044327199,
    0.06690841799917835,
    0.5697662305401315,
    1.1717415299138232,
    0.165438284650696,
    -0.043576183809173635,
    -0.6871129768510887
], scale=Interval)

print("p-value of ex_ttest_ind_eq(d1, d2):  %f" % ex_ttest_ind_eq(d1, d2))

# % ./env-why3 python3 ./examples/statwhy-python/hypothesis_testing/ex_ttest_ind_eq.py 
# p-value of ex_ttest_ind_eq(d1, d2):  0.472670
