from statwhy import Nil, Cons, array, string, NormalD, Param, Const, real, Two, dataset, Interval
from statwhy import exec_dunnett

#@ use cameleerBHL.CameleerBHL
#@ use dunnett.Dunnett
#@ use array.Array

p0 = NormalD(Param("mu0"), Const(1.0))
p1 = NormalD(Param("mu1"), Const(1.0))
p2 = NormalD(Param("mu2"), Const(1.0))
p3 = NormalD(Param("mu3"), Const(1.0))

def ex_dunnett3(d1 : dataset[real], d2, d3, c) -> array[real] :
    #@ requires for_all (fun d -> d.scale = Interval) \
    #@                   (Cons d1 (Cons d2 (Cons d3 Nil))) /\ \
    #@          independent_list \
    #@            (Cons d1 (Cons d2 (Cons d3 Nil))) /\ \
    #@          c.scale = Interval /\ \
    #@          !st = Nil /\ \
    #@          for_all2 \
    #@            sampled \
    #@            (Cons d1 (Cons d2 (Cons d3 Nil))) \
    #@            (Cons p1 (Cons p2 (Cons p3 Nil))) /\ \
    #@          sampled c p0 /\ \
    #@          for_all \
    #@            (fun p -> (World !st interp) |= Possible (mean p0 $< mean p) /\ \
    #@                      (World !st interp) |= Possible (mean p0 $> mean p)) \
    #@            (Cons p1 (Cons p2 (Cons p3 Nil)))

    #@  ensures \
    #@    let ps = result in \
    #@    for_all (fun t -> let (i,p) = t in \
    #@              (Eq (ps[i]) = compose_pvs (mean p0 $!= mean p) !st) && \
    #@              (World !st interp |= StatB (Eq (ps[i])) (mean p0 $!= mean p))) \
    #@            (enumerate (Cons p1 (Cons p2 (Cons p3 Nil))) 0)

    return exec_dunnett(Cons(p1, Cons(p2, Cons(p3, Nil))), p0, \
                        Cons(d1, Cons(d2, Cons(d3, Nil))), c, Two)

#@ execution

# from scipy.stats import norm
# for x in norm.rvs(loc=0.0, scale=1.0, size=10) :
#     print(x)
d1 = dataset(data=[
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

# from scipy.stats import norm
# for x in norm.rvs(loc=0.0, scale=1.0, size=10) :
#     print(x)
d2 = dataset(data=[
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

# from scipy.stats import norm
# for x in norm.rvs(loc=0.0, scale=1.0, size=10) :
#     print(x)
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

# from scipy.stats import norm
# for x in norm.rvs(loc=0.0, scale=1.0, size=10) :
#     print(x)
c = dataset(data=[
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

print(ex_dunnett3(d1, d2, d3, c))
