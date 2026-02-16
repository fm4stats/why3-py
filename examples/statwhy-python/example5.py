from statwhy import string, NormalD, Param, real, exec_ttest_1samp, Two
#@ use cameleerBHL.CameleerBHL
#@ use ttest.Ttest

t_n = NormalD(Param("mu1"), Param("var"))

def example5(d1, d2) :
    #@ requires \
    #@   let fmlA_l : formula = mean t_n $< const_term 1.0 in \
    #@   let fmlA_u : formula = mean t_n $> const_term 1.0 in \
    #@   let fmlA   : formula = mean t_n $!= const_term 1.0 in \
    #@   is_empty !st /\ \
    #@   sampled d1 t_n /\ sampled d2 t_n /\ \
    #@   d1.scale = Interval /\ d2.scale = Interval /\ \
    #@   (World !st interp) |= Possible fmlA_l /\ \
    #@   (World !st interp) |= Possible fmlA_u
    #@ ensures \
    #@   let fmlA_l : formula = mean t_n $< const_term 1.0 in \
    #@   let fmlA_u : formula = mean t_n $> const_term 1.0 in \
    #@   let fmlA   : formula = mean t_n $!= const_term 1.0 in \
    #@   let (p1, p2, p) = result in \
    #@   ((Eq p = compose_pvs fmlA !st (* This is incorrect *) \
    #@     && (World !st interp) |= StatB (Eq p) fmlA) && \
    #@    (Leq (p1 +. p2) = compose_pvs fmlA !st (* This is correct *) \
    #@     && (World !st interp) |= StatB (Leq (p1 +. p2)) fmlA))
    p1 = exec_ttest_1samp(t_n, 1.0, d1, Two)
    p2 = exec_ttest_1samp(t_n, 1.0, d2, Two)
    p = min(p1, p2)
    return (p1, p2, p)
