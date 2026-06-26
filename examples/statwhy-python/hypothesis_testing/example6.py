from statwhy import Nil, Cons, string, NormalD, Param, real, Two, dataset, Interval
from statwhy import exec_tukey_hsd

#@ use cameleerBHL.CameleerBHL
#@ use tukey_HSD.Tukey_HSD
#@ use array.Array

t_n1 = NormalD(Param("mu1"), Param("var"))
t_n2 = NormalD(Param("mu2"), Param("var"))
t_n3 = NormalD(Param("mu3"), Param("var"))

# Execute Tukey's HSD test for multiple comparison of 3 groups
def example6_tukey_hsd(d1, d2, d3) :

    #@ requires \
    #@   let t_mu1 = RealT (mean t_n1) in \
    #@   let t_mu2 = RealT (mean t_n2) in \
    #@   let t_mu3 = RealT (mean t_n3) in \
    #@   let terms3 = (Cons t_mu1 (Cons t_mu2 (Cons t_mu3 Nil))) in \
    #@   is_empty (!st) /\ \
    #@   independent_list (Cons d1 (Cons d2 (Cons d3 Nil))) /\ \
    #@   for_all2 \
    #@     sampled \
    #@     (Cons d1 (Cons d2 (Cons d3 Nil))) \
    #@     (Cons t_n1 (Cons t_n2 (Cons t_n3 Nil))) /\ \
    #@   for_all \
    #@     (fun d -> d.scale = Interval) \
    #@     (Cons d1 (Cons d2 (Cons d3 Nil))) /\ \
    #@   for_all (fun fml -> (World !st interp) |= Possible fml) (combinations terms3 "<") /\ \
    #@   for_all (fun fml -> (World !st interp) |= Possible fml) (combinations terms3 ">")

    #@ ensures \
    #@   let t_mu1 = RealT (mean t_n1) in \
    #@   let t_mu2 = RealT (mean t_n2) in \
    #@   let t_mu3 = RealT (mean t_n3) in \
    #@   let terms3 = (Cons t_mu1 (Cons t_mu2 (Cons t_mu3 Nil))) in \
    #@   let ps = result in \
    #@   for_all (fun t -> let (i,fml) = t in \
    #@             (Eq (ps[i]) = compose_pvs fml !st) && \
    #@             (World !st interp |= StatB (Eq (ps[i])) fml)) \
    #@           (enumerate (combinations terms3 "!=") 0)

    return exec_tukey_hsd(Cons(t_n1, Cons(t_n2, Cons(t_n3, Nil))), \
                          Cons(d1, Cons(d2, Cons(d3, Nil))))

#@ execution

y1 = dataset(data=[
    0.766619176600281671,
    1.21789185837721869,
    1.99159246988234928,
    1.60647913567575529,
    1.47148639466940301,
    0.184253105479018964,
    -0.305625265984637684,
    0.391653042798745687,
    0.751061964281471761,
    0.636099333870649319,
], scale=Interval)

y2 = dataset(data=[
    1.33080408985008525,
    0.818096098824745,
    0.358846712280329605,
    2.03612265448292229,
    1.53355196013926487,
    2.86422867768522549,
    0.33717261327312964,
    2.97841750606052269,
    0.911561712359776899,
    1.51455005196473058,
], scale=Interval)

y3 = dataset(data=[
    2.73343897147291148,
    1.73257203436255591,
    0.846962147974803514,
    2.38736316604747723,
    2.99839846928943121,
    2.22163792102414837,
    1.03345074000452164,
    0.336433008189366722,
    2.844524316810912,
    0.911470664085555438,
], scale=Interval)

res = example6_tukey_hsd(y1, y2, y3)
for p in res:
    print("p-value : %f" % p)
