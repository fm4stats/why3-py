string = str

parameter = string

real = float

class real_number :
    pass

def Param(x : parameter) -> real_number :
    raise NotImplementedError

def Const(x : real) -> real_number :
    raise NotImplementedError

class population :
    pass

def NormalD(x1 : real_number, x2 : real_number) -> population :
    raise NotImplementedError

def BernoulliD(x : real_number) -> population :
    raise NotImplementedError

def CategoricalD(x : list[real_number]) -> population :
    raise NotImplementedError

def UnknownD(x : string) -> population :
    raise NotImplementedError

class alternative :
    pass

Two = alternative()
Up = alternative()
Low = alternative()

def exec_ttest_1samp(p : population, mu : real, y : list[real], alt : alternative) -> real :
    raise NotImplementedError
