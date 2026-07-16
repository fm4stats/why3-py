# translated from examples/mlw/ex_cramervonmises.mlw.

from statwhy import Nil, Cons, array, string, UnknownD, NormalD, CategoricalD, Param, Const, real, Two, dataset, Interval
from statwhy import exec_cramervonmises
#@ use cameleerBHL.CameleerBHL
#@ use cramervonmises.Cramervonmises

p1 = UnknownD("p1")
p_null = NormalD(Const(0.1), Const(0.5))

def ex_cramervonmises1(d) -> real:
    #@ requires \
    #@   is_empty !st /\ \
    #@   sampled d p1 /\ d.scale = Interval /\ \
    #@   (World !st interp) |= Possible (p1 $!=^ p_null)

    #@ ensures \
    #@   let p = result in \
    #@   Eq p = compose_pvs (p1 $!=^ p_null) !st && \
    #@   (World !st interp) |= StatB (Eq p) (p1 $!=^ p_null)

    return exec_cramervonmises(p1, p_null, d)

