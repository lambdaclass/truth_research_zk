-- ArithExpr spec exercising `neg`: -x0.
open TRZK (ArithExpr)

def spec : ArithExpr := .neg (.var 0)
