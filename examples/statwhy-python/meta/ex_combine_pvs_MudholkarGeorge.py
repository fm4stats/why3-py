from statwhy import Nil, Cons, real
from statwhy import formula, Disj, sit
from statwhy import exec_combine_pvs_MudholkarGeorge

#@ use cameleerBHL.CameleerBHL
#@ use combine_pvs.CombinePVs
#@ use list.Map

# The ID numbers for 3 experiments
exp1 : real = 1.0
exp2 : real = 2.0
exp3 : real = 3.0
exps : list[real] = Cons(exp1, Cons(exp2, Cons(exp3, Nil)))

# The disjunctive formula representing one of the three situations
disj_exps : formula = Disj(sit(exp1), Disj(sit(exp2), sit(exp3)))

# Executes Mudholkar-George's method for combining 3 p-values.
def ex_combine_pvs_MudholkarGeorge(pv1: real, pv2 : real, pv3 : real, fml: formula) -> real :
    #@  requires \
    #@    let pvs  = Cons pv1 (Cons pv2 (Cons pv3 Nil)) in \
    #@    pvalues pvs /\ \
    #@    let d : dataset real = { data = pvs; scale = Interval } in \
    #@    sampled d uniform_pv /\ (* Each p-value in d is sampled uniformly & independently. *) \
    #@    intend_to_detect_excess_of_small_and_large_pv /\ \
    #@    (* The statistical belief on fml under the situation (sit exp) where each experiment exp has done. *) \
    #@    for_all2 (fun pv exp -> (exists w' : world. w' |= StatB (Eq pv) (Impl (sit exp) fml))) pvs exps

    #@  ensures \
    #@    pvalue result /\ \
    #@    (World !st interp |= StatB (Eq result) (Impl disj_exps fml))

    pvs = Cons(pv1, Cons(pv2, Cons(pv3, Nil)))
    return exec_combine_pvs_MudholkarGeorge(pvs, exps, disj_exps, fml)

#@ execution

# The p-values for the 3 experiments
pv1 : real = 0.1
pv2 : real = 0.2
pv3 : real = 0.3

# The dummy alternative hypothesis
fml = formula()

res = ex_combine_pvs_MudholkarGeorge(pv1, pv2, pv3, fml)
print("ex_combine_pvs_MudholkarGeorge p-value : %f" % res)
