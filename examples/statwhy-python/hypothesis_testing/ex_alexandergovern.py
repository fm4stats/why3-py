# translated from examples/mlw/ex_alexandergovern.mlw.

from statwhy import Nil, Cons, array, string, NormalD, Param, real, Two, dataset, Interval
from statwhy import exec_alexandergovern
#@ use cameleerBHL.CameleerBHL
#@ use alexandergovern.AlexanderGovern

p1 = NormalD(Param("mean1"), Param("var1"))
p2 = NormalD(Param("mean2"), Param("var2"))
p3 = NormalD(Param("mean3"), Param("var3"))
p4 = NormalD(Param("mean4"), Param("var4"))

def ex_alexandergovern4(d1, d2, d3, d4) -> real:
    #@ requires \
    #@   let t_m1 = mean p1 in \
    #@   let t_m2 = mean p2 in \
    #@   let t_m3 = mean p3 in \
    #@   let t_m4 = mean p4 in \
    #@   independent_list (Cons d1 (Cons d2 (Cons d3 (Cons d4 Nil)))) /\ \
    #@   for_all (fun d -> d.scale = Interval) (Cons d1 (Cons d2 (Cons d3 (Cons d4 Nil)))) /\ \
    #@   is_empty !st /\ \
    #@   for_all2 \
    #@     (fun p y -> sampled y p) \
    #@     (Cons p1 (Cons p2 (Cons p3 (Cons p4 Nil)))) \
    #@     (Cons d1 (Cons d2 (Cons d3 (Cons d4 Nil)))) /\ \
    #@   ((World !st interp) |= Possible (t_m1 $< t_m2)) /\ \
    #@   ((World !st interp) |= Possible (t_m1 $> t_m2)) /\ \
    #@   ((World !st interp) |= Possible (t_m1 $< t_m3)) /\ \
    #@   ((World !st interp) |= Possible (t_m1 $> t_m3)) /\ \
    #@   ((World !st interp) |= Possible (t_m1 $< t_m4)) /\ \
    #@   ((World !st interp) |= Possible (t_m1 $> t_m4)) /\ \
    #@   ((World !st interp) |= Possible (t_m2 $< t_m3)) /\ \
    #@   ((World !st interp) |= Possible (t_m2 $> t_m3)) /\ \
    #@   ((World !st interp) |= Possible (t_m2 $< t_m4)) /\ \
    #@   ((World !st interp) |= Possible (t_m2 $> t_m4)) /\ \
    #@   ((World !st interp) |= Possible (t_m3 $< t_m4)) /\ \
    #@   ((World !st interp) |= Possible (t_m3 $> t_m4))

    #@ ensures \
    #@   let p = result in \
    #@   let t_m1 = mean p1 in \
    #@   let t_m2 = mean p2 in \
    #@   let t_m3 = mean p3 in \
    #@   let t_m4 = mean p4 in \
    #@   let h = (t_m1 $!= t_m2) $|| (t_m1 $!= t_m3) $|| (t_m1 $!= t_m4) \
    #@       $|| (t_m2 $!= t_m3) $|| (t_m2 $!= t_m4) $|| (t_m3 $!= t_m4) in \
    #@   Eq p = compose_pvs h !st && \
    #@   (World !st interp) |= StatB (Eq p) h

    return exec_alexandergovern(Cons(p1, Cons(p2, Cons(p3, Cons(p4, Nil)))), Cons(d1, Cons(d2, Cons(d3, Cons(d4, Nil)))))


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

d3 = dataset(data=[
    0.35565342105533765,
    1.118789791385098,
    -0.2039206869327654,
    -0.4261762987954533,
    0.014075351102537808,
    -0.16323247950391698,
    0.3151510396487179,
    0.6306254069141548,
    -0.8988584700113046,
    -0.4016508941780488
], scale=Interval)

d4 = dataset(data=[
    -0.45564457363750654,
    -1.288488313162085,
    -0.16940356152901212,
    1.0227620610356287,
    0.030686999219211412,
    -0.4052554329848597,
    -0.5166124981377371,
    0.4675915440436093,
    -1.0272338221562711,
    -0.11488017884405187
], scale=Interval)

print("p-value: %f" % ex_alexandergovern4(d1, d2, d3, d4))

# % ./env-why3 python3 ./examples/statwhy-python/hypothesis_testing/ex_alexandergovern.py
# p-value: 0.629888
