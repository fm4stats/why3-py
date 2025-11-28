from statwhy import string, NormalD, Param, real, exec_ttest_1samp, Two
#@ use cameleerBHL.CameleerBHL
#@ use ttest.Ttest

p1 = NormalD(Param("mu1"), Param("var"))
p2 = NormalD(Param("mu2"), Param("var"))
p3 = NormalD(Param("mu3"), Param("var"))
p4 = NormalD(Param("mu4"), Param("var"))
p5 = NormalD(Param("mu5"), Param("var"))
p6 = NormalD(Param("mu6"), Param("var"))

def ex_six_hypotheses_disj(d1, d2, d3, d4, d5, d6) -> real :
    #@ requires \
    #@  is_empty !st /\ \
    #@  sampled d1 p1 /\ sampled d2 p2 /\ sampled d3 p3 /\ sampled d4 p4 /\ sampled d5 p5 /\ sampled d6 p6 /\ \
    #@  (World !st interp) |= Possible (mean p1 $< const_term 1.0) /\ \
    #@  (World !st interp) |= Possible (mean p1 $> const_term 1.0) /\ \
    #@  (World !st interp) |= Possible (mean p2 $< const_term 2.0) /\ \
    #@  (World !st interp) |= Possible (mean p2 $> const_term 2.0) /\ \
    #@  (World !st interp) |= Possible (mean p3 $< const_term 3.0) /\ \
    #@  (World !st interp) |= Possible (mean p3 $> const_term 3.0) /\ \
    #@  (World !st interp) |= Possible (mean p4 $< const_term 4.0) /\ \
    #@  (World !st interp) |= Possible (mean p4 $> const_term 4.0) /\ \
    #@  (World !st interp) |= Possible (mean p5 $< const_term 5.0) /\ \
    #@  (World !st interp) |= Possible (mean p5 $> const_term 5.0) /\ \
    #@  (World !st interp) |= Possible (mean p6 $< const_term 6.0) /\ \
    #@  (World !st interp) |= Possible (mean p6 $> const_term 6.0)

    #@ ensures \
    #@  let p = result in \
    #@  (Leq p) = compose_pvs \
    #@              ((mean p1 $!= const_term 1.0) \
    #@               $|| (mean p2 $!= const_term 2.0) \
    #@               $|| (mean p3 $!= const_term 3.0) \
    #@               $|| (mean p4 $!= const_term 4.0) \
    #@               $|| (mean p5 $!= const_term 5.0) \
    #@               $|| (mean p6 $!= const_term 6.0) \
    #@              ) !st && \
    #@  (World !st interp) |= StatB (Leq p) ((mean p1 $!= const_term 1.0) \
    #@                                       $|| (mean p2 $!= const_term 2.0) \
    #@                                       $|| (mean p3 $!= const_term 3.0) \
    #@                                       $|| (mean p4 $!= const_term 4.0) \
    #@                                       $|| (mean p5 $!= const_term 5.0) \
    #@                                       $|| (mean p6 $!= const_term 6.0) \
    #@                                      )

    r1 = exec_ttest_1samp(p1, 1.0, d1, Two)
    r2 = exec_ttest_1samp(p2, 2.0, d2, Two)
    r3 = exec_ttest_1samp(p3, 3.0, d3, Two)
    r4 = exec_ttest_1samp(p4, 4.0, d4, Two)
    r5 = exec_ttest_1samp(p5, 5.0, d5, Two)
    r6 = exec_ttest_1samp(p6, 6.0, d6, Two)
    return r1 + r2 + r3 + r4 + r5 + r6

def ex_six_hypotheses_conj(d1, d2, d3, d4, d5, d6) -> real :
    #@ requires \
    #@  is_empty !st /\ \
    #@  sampled d1 p1 /\ sampled d2 p2 /\ sampled d3 p3 /\ sampled d4 p4 /\ sampled d5 p5 /\ sampled d6 p6 /\ \
    #@  (World !st interp) |= Possible (mean p1 $< const_term 1.0) /\ \
    #@  (World !st interp) |= Possible (mean p1 $> const_term 1.0) /\ \
    #@  (World !st interp) |= Possible (mean p2 $< const_term 2.0) /\ \
    #@  (World !st interp) |= Possible (mean p2 $> const_term 2.0) /\ \
    #@  (World !st interp) |= Possible (mean p3 $< const_term 3.0) /\ \
    #@  (World !st interp) |= Possible (mean p3 $> const_term 3.0) /\ \
    #@  (World !st interp) |= Possible (mean p4 $< const_term 4.0) /\ \
    #@  (World !st interp) |= Possible (mean p4 $> const_term 4.0) /\ \
    #@  (World !st interp) |= Possible (mean p5 $< const_term 5.0) /\ \
    #@  (World !st interp) |= Possible (mean p5 $> const_term 5.0) /\ \
    #@  (World !st interp) |= Possible (mean p6 $< const_term 6.0) /\ \
    #@  (World !st interp) |= Possible (mean p6 $> const_term 6.0)

    #@ ensures \
    #@  let p = result in \
    #@  (Leq p) = compose_pvs \
    #@              ((mean p1 $!= const_term 1.0) \
    #@               $&& (mean p2 $!= const_term 2.0) \
    #@               $&& (mean p3 $!= const_term 3.0) \
    #@               $&& (mean p4 $!= const_term 4.0) \
    #@               $&& (mean p5 $!= const_term 5.0) \
    #@               $&& (mean p6 $!= const_term 6.0) \
    #@              ) !st && \
    #@  (World !st interp) |= StatB (Leq p) ((mean p1 $!= const_term 1.0) \
    #@                                       $&& (mean p2 $!= const_term 2.0) \
    #@                                       $&& (mean p3 $!= const_term 3.0) \
    #@                                       $&& (mean p4 $!= const_term 4.0) \
    #@                                       $&& (mean p5 $!= const_term 5.0) \
    #@                                       $&& (mean p6 $!= const_term 6.0) \
    #@                                       )

    r1 = exec_ttest_1samp(p1, 1.0, d1, Two)
    r2 = exec_ttest_1samp(p2, 2.0, d2, Two)
    r3 = exec_ttest_1samp(p3, 3.0, d3, Two)
    r4 = exec_ttest_1samp(p4, 4.0, d4, Two)
    r5 = exec_ttest_1samp(p5, 5.0, d5, Two)
    r6 = exec_ttest_1samp(p6, 6.0, d6, Two)
    return min(min(min(min(min(r1, r2), r3), r4), r5), r6)
