from statwhy import string, NormalD, Param, real, exec_ttest_1samp, Two, dataset, Interval
#@ use cameleerBHL.CameleerBHL
#@ use ttest.Ttest

# Declarations of a distribution and formulas
t_n = NormalD(Param("mu1"), Param("var"))

# executes the t-test for a population mean
def example1(d : dataset[real]) :
    #@ requires \
    #@   let fmlA_l = mean t_n $< const_term 1.0 in \
    #@   let fmlA_u = mean t_n $> const_term 1.0 in \
    #@   let fmlA = mean t_n $!= const_term 1.0 in \
    #@   is_empty (!st) /\ \
    #@   sampled d t_n /\ \
    #@   d.scale = Interval /\ \
    #@   (World (!st) interp) |= Possible fmlA_l /\ \
    #@   (World (!st) interp) |= Possible fmlA_u
    #@ ensures \
    #@   let fmlA_l = mean t_n $< const_term 1.0 in \
    #@   let fmlA_u = mean t_n $> const_term 1.0 in \
    #@   let fmlA = mean t_n $!= const_term 1.0 in \
    #@   let p = result in \
    #@   Eq p = compose_pvs fmlA !st && \
    #@   (World !st interp) |= StatB (Eq p) fmlA
    return exec_ttest_1samp(t_n, 1.0, d, Two)

#@ execution

d = dataset(data=[
    0.172199288696712305,
    1.56633241273914514,
    -1.46459260193754326,
    -1.43755987448188516,
    0.606597055392836,
    -0.858854622560882852,
    0.830966186381477567,
    -0.0902063463539077848,
    0.0151171772866927571,
    -1.29692214960254959,
    -1.49792102111270431,
    0.517798308025511522,
    -0.192132041057335529,
    -0.162761486272442774,
    -1.54871151183215727,
], scale=Interval)
print("p-value : %f" % example1(d))


