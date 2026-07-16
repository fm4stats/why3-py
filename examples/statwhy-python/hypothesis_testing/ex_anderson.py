# translated from examples/mlw/ex_anderson.mlw.

from statwhy import Nil, Cons, array, string, UnknownD, Param, real, Two, dataset, Interval
from statwhy import exec_anderson, Norm, Expon, Logistic
#@ use cameleerBHL.CameleerBHL
#@ use anderson.Anderson

d1 = UnknownD("d1")

def ex_anderson1(y) -> real:
    #@ requires \
    #@   is_empty !st /\ \
    #@   y.scale = Interval /\ \
    #@   (World !st interp) |= is_continuous d1 /\ \
    #@   sampled y d1 /\ \
    #@   (World !st interp) |= Possible (Not (is_exponential d1))

    #@ ensures \
    #@   let p = result in \
    #@   Leq p = compose_pvs (Not (is_exponential d1)) !st && \
    #@   (World !st interp) |= StatB (Leq p) (Not (is_exponential d1))

    return exec_anderson(d1, y, Expon)


#@ execution

data = dataset(data=[
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

print("p-value: %f" % ex_anderson1(data))

# % ./env-why3 python3 ./examples/statwhy-python/hypothesis_testing/ex_anderson.py 
# p-value: 0.010000
