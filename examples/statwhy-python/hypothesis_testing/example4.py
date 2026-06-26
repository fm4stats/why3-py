from statwhy import string, NormalD, Param, real, Two, dataset, Interval
from statwhy import exec_ttest_ind_eq

#@ use cameleerBHL.CameleerBHL
#@ use ttest.Ttest

t_n1 = NormalD(Param("mu1"), Param("var"))
t_n2 = NormalD(Param("mu2"), Param("var"))
t_n3 = NormalD(Param("mu3"), Param("var"))

# H1 : (fmlA \/ fmlB) \/ fmlC
def example_or_or(d1, d2, d3) -> real :
    #@ requires \
    #@   let fmlA_l = mean t_n1 $< mean t_n2 in \
    #@   let fmlA_u = mean t_n1 $> mean t_n2 in \
    #@   let fmlA = mean t_n1 $!= mean t_n2 in \
    #@   let fmlB_l = mean t_n1 $< mean t_n3 in \
    #@   let fmlB_u = mean t_n1 $> mean t_n3 in \
    #@   let fmlB = mean t_n1 $!= mean t_n3 in \
    #@   let fmlC_l = mean t_n2 $< mean t_n3 in \
    #@   let fmlC_u = mean t_n2 $> mean t_n3 in \
    #@   let fmlC = mean t_n2 $!= mean t_n3 in \
    #@   let fml_or_or = fmlA $|| fmlB $|| fmlC in \
    #@   let fml_and_or = fmlA $&& fmlB $|| fmlC in \
    #@   let fml_or_and = fmlA $|| fmlB $&& fmlC in \
    #@   let fml_and_and = fmlA $&& fmlB $&& fmlC in \
    #@   is_empty (!st) /\ \
    #@   sampled d1 t_n1 /\ sampled d2 t_n2 /\ sampled d3 t_n3 /\ \
    #@   d1.scale = d2.scale = d3.scale = Interval /\ \
    #@   independent d1 d2 /\ independent d1 d3 /\ independent d2 d3 /\ \
    #@   (World (!st) interp) |= Possible fmlA_l /\ \
    #@   (World (!st) interp) |= Possible fmlA_u /\ \
    #@   (World (!st) interp) |= Possible fmlB_l /\ \
    #@   (World (!st) interp) |= Possible fmlB_u /\ \
    #@   (World (!st) interp) |= Possible fmlC_l /\ \
    #@   (World (!st) interp) |= Possible fmlC_u
    #@ ensures \
    #@   let fmlA_l = mean t_n1 $< mean t_n2 in \
    #@   let fmlA_u = mean t_n1 $> mean t_n2 in \
    #@   let fmlA = mean t_n1 $!= mean t_n2 in \
    #@   let fmlB_l = mean t_n1 $< mean t_n3 in \
    #@   let fmlB_u = mean t_n1 $> mean t_n3 in \
    #@   let fmlB = mean t_n1 $!= mean t_n3 in \
    #@   let fmlC_l = mean t_n2 $< mean t_n3 in \
    #@   let fmlC_u = mean t_n2 $> mean t_n3 in \
    #@   let fmlC = mean t_n2 $!= mean t_n3 in \
    #@   let fml_or_or = fmlA $|| fmlB $|| fmlC in \
    #@   let fml_and_or = fmlA $&& fmlB $|| fmlC in \
    #@   let fml_or_and = fmlA $|| fmlB $&& fmlC in \
    #@   let fml_and_and = fmlA $&& fmlB $&& fmlC in \
    #@   let p = result in \
    #@   (Leq p) = compose_pvs fml_or_or !st && \
    #@   (World !st interp) |= StatB (Leq p) ((((mean t_n1) $!= (mean t_n2)) $|| fmlB) $|| fmlC)
    p1 = exec_ttest_ind_eq(t_n1, t_n2, d1, d2, Two)
    p2 = exec_ttest_ind_eq(t_n1, t_n3, d1, d3, Two)
    p3 = exec_ttest_ind_eq(t_n2, t_n3, d2, d3, Two)
    return p1 + p2 + p3

# H1 : (fmlA /\ fmlB) \/ fmlC
def example_and_or(d1, d2, d3) -> real :
    #@ requires \
    #@   let fmlA_l = mean t_n1 $< mean t_n2 in \
    #@   let fmlA_u = mean t_n1 $> mean t_n2 in \
    #@   let fmlA = mean t_n1 $!= mean t_n2 in \
    #@   let fmlB_l = mean t_n1 $< mean t_n3 in \
    #@   let fmlB_u = mean t_n1 $> mean t_n3 in \
    #@   let fmlB = mean t_n1 $!= mean t_n3 in \
    #@   let fmlC_l = mean t_n2 $< mean t_n3 in \
    #@   let fmlC_u = mean t_n2 $> mean t_n3 in \
    #@   let fmlC = mean t_n2 $!= mean t_n3 in \
    #@   let fml_or_or = fmlA $|| fmlB $|| fmlC in \
    #@   let fml_and_or = fmlA $&& fmlB $|| fmlC in \
    #@   let fml_or_and = fmlA $|| fmlB $&& fmlC in \
    #@   let fml_and_and = fmlA $&& fmlB $&& fmlC in \
    #@   is_empty (!st) /\ \
    #@   sampled d1 t_n1 /\ sampled d2 t_n2 /\ sampled d3 t_n3 /\ \
    #@   d1.scale = d2.scale = d3.scale = Interval /\ \
    #@   independent d1 d2 /\ independent d1 d3 /\ independent d2 d3 /\ \
    #@   (World (!st) interp) |= Possible fmlA_l /\ \
    #@   (World (!st) interp) |= Possible fmlA_u /\ \
    #@   (World (!st) interp) |= Possible fmlB_l /\ \
    #@   (World (!st) interp) |= Possible fmlB_u /\ \
    #@   (World (!st) interp) |= Possible fmlC_l /\ \
    #@   (World (!st) interp) |= Possible fmlC_u
    #@ ensures \
    #@   let fmlA_l = mean t_n1 $< mean t_n2 in \
    #@   let fmlA_u = mean t_n1 $> mean t_n2 in \
    #@   let fmlA = mean t_n1 $!= mean t_n2 in \
    #@   let fmlB_l = mean t_n1 $< mean t_n3 in \
    #@   let fmlB_u = mean t_n1 $> mean t_n3 in \
    #@   let fmlB = mean t_n1 $!= mean t_n3 in \
    #@   let fmlC_l = mean t_n2 $< mean t_n3 in \
    #@   let fmlC_u = mean t_n2 $> mean t_n3 in \
    #@   let fmlC = mean t_n2 $!= mean t_n3 in \
    #@   let fml_or_or = fmlA $|| fmlB $|| fmlC in \
    #@   let fml_and_or = fmlA $&& fmlB $|| fmlC in \
    #@   let fml_or_and = fmlA $|| fmlB $&& fmlC in \
    #@   let fml_and_and = fmlA $&& fmlB $&& fmlC in \
    #@   let p = result in \
    #@   (Leq p) = compose_pvs fml_and_or !st && \
    #@   (World !st interp) |= StatB (Leq p) fml_and_or
    p1 = exec_ttest_ind_eq(t_n1, t_n2, d1, d2, Two)
    p2 = exec_ttest_ind_eq(t_n1, t_n3, d1, d3, Two)
    p3 = exec_ttest_ind_eq(t_n2, t_n3, d2, d3, Two)
    return min(p1, p2) + p3

# H1 : (fmlA \/ fmlB) \/ fmlC
def example_or_and(d1, d2, d3) -> real :
    #@  requires \
    #@    let fmlA_l = mean t_n1 $< mean t_n2 in \
    #@    let fmlA_u = mean t_n1 $> mean t_n2 in \
    #@    let fmlA = mean t_n1 $!= mean t_n2 in \
    #@    let fmlB_l = mean t_n1 $< mean t_n3 in \
    #@    let fmlB_u = mean t_n1 $> mean t_n3 in \
    #@    let fmlB = mean t_n1 $!= mean t_n3 in \
    #@    let fmlC_l = mean t_n2 $< mean t_n3 in \
    #@    let fmlC_u = mean t_n2 $> mean t_n3 in \
    #@    let fmlC = mean t_n2 $!= mean t_n3 in \
    #@    let fml_or_or = fmlA $|| fmlB $|| fmlC in \
    #@    let fml_and_or = fmlA $&& fmlB $|| fmlC in \
    #@    let fml_or_and = fmlA $|| fmlB $&& fmlC in \
    #@    let fml_and_and = fmlA $&& fmlB $&& fmlC in \
    #@    is_empty (!st) /\ \
    #@    sampled d1 t_n1 /\ sampled d2 t_n2 /\ sampled d3 t_n3 /\ \
    #@    d1.scale = d2.scale = d3.scale = Interval /\ \
    #@    independent d1 d2 /\ independent d1 d3 /\ independent d2 d3 /\ \
    #@    (World (!st) interp) |= Possible fmlA_l /\ \
    #@    (World (!st) interp) |= Possible fmlA_u /\ \
    #@    (World (!st) interp) |= Possible fmlB_l /\ \
    #@    (World (!st) interp) |= Possible fmlB_u /\ \
    #@    (World (!st) interp) |= Possible fmlC_l /\ \
    #@    (World (!st) interp) |= Possible fmlC_u
    #@  ensures \
    #@    let fmlA_l = mean t_n1 $< mean t_n2 in \
    #@    let fmlA_u = mean t_n1 $> mean t_n2 in \
    #@    let fmlA = mean t_n1 $!= mean t_n2 in \
    #@    let fmlB_l = mean t_n1 $< mean t_n3 in \
    #@    let fmlB_u = mean t_n1 $> mean t_n3 in \
    #@    let fmlB = mean t_n1 $!= mean t_n3 in \
    #@    let fmlC_l = mean t_n2 $< mean t_n3 in \
    #@    let fmlC_u = mean t_n2 $> mean t_n3 in \
    #@    let fmlC = mean t_n2 $!= mean t_n3 in \
    #@    let fml_or_or = fmlA $|| fmlB $|| fmlC in \
    #@    let fml_and_or = fmlA $&& fmlB $|| fmlC in \
    #@    let fml_or_and = fmlA $|| fmlB $&& fmlC in \
    #@    let fml_and_and = fmlA $&& fmlB $&& fmlC in \
    #@    let p = result in \
    #@    (Leq p) = compose_pvs fml_or_and !st && \
    #@    (World !st interp) |= StatB (Leq p) fml_or_and
    p1 = exec_ttest_ind_eq(t_n1, t_n2, d1, d2, Two)
    p2 = exec_ttest_ind_eq(t_n1, t_n3, d1, d3, Two)
    p3 = exec_ttest_ind_eq(t_n2, t_n3, d2, d3, Two)
    return min(p1 + p2, p3)

# H1 : (fmlA /\ fmlB) /\ fmlC
def example_and_and(d1, d2, d3) :
    #@ requires \
    #@   let fmlA_l = mean t_n1 $< mean t_n2 in \
    #@   let fmlA_u = mean t_n1 $> mean t_n2 in \
    #@   let fmlA = mean t_n1 $!= mean t_n2 in \
    #@   let fmlB_l = mean t_n1 $< mean t_n3 in \
    #@   let fmlB_u = mean t_n1 $> mean t_n3 in \
    #@   let fmlB = mean t_n1 $!= mean t_n3 in \
    #@   let fmlC_l = mean t_n2 $< mean t_n3 in \
    #@   let fmlC_u = mean t_n2 $> mean t_n3 in \
    #@   let fmlC = mean t_n2 $!= mean t_n3 in \
    #@   let fml_or_or = fmlA $|| fmlB $|| fmlC in \
    #@   let fml_and_or = fmlA $&& fmlB $|| fmlC in \
    #@   let fml_or_and = fmlA $|| fmlB $&& fmlC in \
    #@   let fml_and_and = fmlA $&& fmlB $&& fmlC in \
    #@   is_empty (!st) /\ \
    #@   sampled d1 t_n1 /\ sampled d2 t_n2 /\ sampled d3 t_n3 /\ \
    #@   d1.scale = d2.scale = d3.scale = Interval /\ \
    #@   independent d1 d2 /\ independent d1 d3 /\ independent d2 d3 /\ \
    #@   (World (!st) interp) |= Possible fmlA_l /\ \
    #@   (World (!st) interp) |= Possible fmlA_u /\ \
    #@   (World (!st) interp) |= Possible fmlB_l /\ \
    #@   (World (!st) interp) |= Possible fmlB_u /\ \
    #@   (World (!st) interp) |= Possible fmlC_l /\ \
    #@   (World (!st) interp) |= Possible fmlC_u
    #@ ensures \
    #@   let fmlA_l = mean t_n1 $< mean t_n2 in \
    #@   let fmlA_u = mean t_n1 $> mean t_n2 in \
    #@   let fmlA = mean t_n1 $!= mean t_n2 in \
    #@   let fmlB_l = mean t_n1 $< mean t_n3 in \
    #@   let fmlB_u = mean t_n1 $> mean t_n3 in \
    #@   let fmlB = mean t_n1 $!= mean t_n3 in \
    #@   let fmlC_l = mean t_n2 $< mean t_n3 in \
    #@   let fmlC_u = mean t_n2 $> mean t_n3 in \
    #@   let fmlC = mean t_n2 $!= mean t_n3 in \
    #@   let fml_or_or = fmlA $|| fmlB $|| fmlC in \
    #@   let fml_and_or = fmlA $&& fmlB $|| fmlC in \
    #@   let fml_or_and = fmlA $|| fmlB $&& fmlC in \
    #@   let fml_and_and = fmlA $&& fmlB $&& fmlC in \
    #@   let p = result in \
    #@   (Leq p) = compose_pvs fml_and_and !st && \
    #@   (World !st interp) |= StatB (Leq p) fml_and_and
    p1 = exec_ttest_ind_eq(t_n1, t_n2, d1, d2, Two)
    p2 = exec_ttest_ind_eq(t_n1, t_n3, d1, d3, Two)
    p3 = exec_ttest_ind_eq(t_n2, t_n3, d2, d3, Two)
    return min(min(p1, p2), p3)

#@ execution

y1 = dataset(data=[
  1.79641027917486484,
  2.15771934160298429,
  0.744049675823909462,
  1.85632680717120024,
  0.960269143630828492,
  1.39403604918404511,
  -0.906289151688035366,
  1.80867759957434071,
  1.34697861125076113,
  -0.371146977565569358,
], scale=Interval)

y2 = dataset(data=[
  2.00283861137070396,
  1.6857945944247883,
  0.935859705215766,
  2.10941742570267,
  1.8444619950554153,
  0.820154195385705775,
  2.49840053635987092,
  1.39786287120975938,
  2.04806561818151245,
  1.85563080881194864,
], scale=Interval)

y3 = dataset(data=[
  2.22468795346111614,
  2.68644951495416207,
  2.12892411618697119,
  0.377463426480728614,
  1.45891395722125661,
  1.37356460379584444,
  1.00344294258386757,
  1.65034332791316829,
  3.03837409085832,
  1.24697412968412613,
], scale=Interval)

res = example_and_and(y1, y2, y3)
print("p-value : %f" % res)
