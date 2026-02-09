from statwhy import string, NormalD, Param, real, exec_ttest_paired, Two
#@ use cameleerBHL.CameleerBHL
#@ use ttest.Ttest

t_n1 = NormalD(Param("mu1"), Param("var1"))
t_n2 = NormalD(Param("mu2"), Param("var2"))

def example2(d1, d2) -> real :
    #@ requires \
    #@    let fmlA_l : formula = mean t_n1 $< mean t_n2 in \
    #@    let fmlA_u : formula = mean t_n1 $> mean t_n2 in \
    #@    let fmlA   : formula = mean t_n1 $!= mean t_n2 in \
    #@    is_empty !st /\ \
    #@    paired d1 d2 /\ \
    #@    d1.scale = Interval /\ d2.scale = Interval /\ \
    #@    sampled d1 t_n1 /\ sampled d2 t_n2 /\ \
    #@    (World !st interp) |= Possible fmlA_l /\ \
    #@    (World !st interp) |= Possible fmlA_u

    #@ ensures \
    #@    let fmlA_l : formula = mean t_n1 $< mean t_n2 in \
    #@    let fmlA_u : formula = mean t_n1 $> mean t_n2 in \
    #@    let fmlA   : formula = mean t_n1 $!= mean t_n2 in \
    #@    let p = result in \
    #@    Eq p = compose_pvs fmlA !st && \
    #@    (World !st interp) |= StatB (Eq p) fmlA

    return exec_ttest_paired(t_n1, t_n2, d1, d2, Two)

#@ execution

y1 = [ \
  0.602625786295998389, \
  2.14566916029819144, \
  1.35823522315676626, \
  1.17182034121895451, \
  2.73483412251327973, \
  0.748574993793243215, \
  -1.23872899202434184, \
  1.13256387540348635, \
  2.13263167487555538, \
  -0.690867157847799 \
]

y2 : list[real] = [ \
  1.20573474164759054, \
  2.72478620692767493, \
  1.72478774466419971, \
  1.52252941317296231, \
  3.27225924826821712, \
  1.39473479558607627, \
  -0.944372818453007135, \
  1.64193391204925154, \
  2.54602531474281335, \
  -0.0302616181108142923 \
]

res = example2(y1, y2)
print("p-value : %f" % res)

