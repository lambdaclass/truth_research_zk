-- ArithExpr spec exercising `sub`: x0 - x1.
open TRZK (ArithExpr)

def spec : ArithExpr := .sub (.var 0) (.var 1)
