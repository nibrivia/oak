from typing import List, Tuple, Optional
from typing_extensions import Self

test_string = """
1
'Hello

(+ 1 2)

(judge 1 Int)

(judge a Int)
(define a 21)

(+ a 1)

((lambda (x) x) 2)

(defun (b) 5)
(b)
(judge b (-> Int))




(judge id (-> Int Int))
(defun (id x) x)
(id 4)


-- (judge sum Int)
(define sum (+ 1 1))

sum

a

(+ 1 1)

(defun (fib x) ( if (<= x 1) 1 (+ (fib (- x 1)) (fib (- x 2)))))

(fib 6)

-- (judge square (-> Int Int))
(define square
    (lambda (val)
     (* val val)))

(square 2)
(square a)


-- (judge r2 (-> Int Int Int)))
(define r2 (lambda (x y)
    (let
        ((x2) (square x))
         ((+ x2 (square y)))
     )))
"""

_ = """
(judge Bool Type)
(define Bool 
    (oneOf
     (('True)
      ('False))))

(judge Maybe (-> Type Type))
(define Maybe
    (lambda (t)
        (oneOf
            (`Nothing)
            (forall (value t) (`Something t))
         )
     )
 )
"""
            

list_string = """
List: Type -> Type
List t =
    Empty:(List t)
    | Cons:(t -> List t -> List t) head tail

"""


class Env:
    def __init__(self, parent = None, bindings = {}):
        self.bindings = {k:v for k, v in bindings.items()}
        self.judgements = {}
        self.parent = parent

    def get(self, name: str):
        if name in self.bindings:
            return self.bindings[name]

        if self.parent is not None:
            return self.parent.get(name)

        raise Exception(f"Name '{name}' not found at the root env")

    def has(self, name:str) -> bool:
        if name in self.bindings:
            return True

        if self.parent is not None:
            return self.parent.has(name)

        return False

    def set_judgement(self, name: str, judgement):
        if name in self.judgements:
            # TODO allow multiple judgements?
            raise Exception(f"{name} already has a judgement")

        if self.has(name):
            self.check_judgement(name, self.get(name), judgement)


        self.judgements[name] = judgement

    def get_judgement(self, name: str):
        if name in self.judgements:
            return self.judgements[name]

    def set_axiom(self, name, judgement):
        self.judgements[name] = judgement

    def check_judgement(self, name: str, value, judgement) -> None:
        childEnv = self.makeChild()
        childEnv.set(name, value)

        if not judgement.verify(childEnv):
            raise Exception(f"Judgement for @{name} does not check out")



    def set(self, name:str, value) -> None:
        if name in self.judgements:
            self.check_judgement(name, value, self.judgements[name])

        if name in self.bindings:
            raise Exception(f"Can't overwrite {name}")

        self.bindings[name] = value


    def makeChild(self):
        child = Env(parent = self)
        return child



def mul(x, y):
    return Value(x.value * y.value)

def add(x, y):
    return Value(x.value + y.value)

def sub(x, y):
    return Value(x.value - y.value)

def lte(x, y):
    return Value(x.value <= y.value)

def lt(x, y):
    return Value(x.value < y.value)

def eq(x, y):
    return Value(x.value == y.value)

def arrow_type(*types):
    return list(types)



class Expression:
    def __init__(self):
        self.annotation = None

    def inferType(self, env: Env) -> Optional[str]:
        return self.annotation


    def evaluate(self, env: Env) -> Tuple[Optional[Self], Env]:
        raise NotImplemented()

    def checkType(self, annotatedType, env:Env) -> bool:
        if self.annotation is not None and annotatedType == self.annotation:
            return True

        inferedType = self.inferType(env)
        if inferedType is not None:
            self.annotation = inferedType
            return self.checkType(annotatedType, env)

        # self.annotation = annotatedType
        raise NotImplemented()


class Value(Expression):
    def __init__(self, value, typ = None):
        super().__init__()

        self.value = value

        if typ is not None:
            self.annotation = typ
        elif isinstance(value, bool):
            self.annotation =  Value("Bool", "Type")
        elif isinstance(value, int):
            self.annotation =  Value("Int", "Type")
        elif isinstance(value, str):
            if value.startswith("'"):
                self.annotation =  Value("Str", "Type")
            if value in ["Bool", "Str", "Int", "Type"]:
                self.annotation = Value("Type", "Type")


    def evaluate(self, env: Env) -> Tuple[Optional[Expression], Env]:
        return (self, env)

    def inferType(self, env):
        return self.annotation

    def checkType(self, annotatedType, env):
        return self.annotation == annotatedType

    def __eq__(self, other) -> bool:
        return self.annotation == other.annotation and self.value == other.value

    def __str__(self):
        if self.annotation is not None:
            return f"{self.value} [{self.annotation}]"
        return str(self.value)


class IfStatement(Expression):
    def __init__(self, condExpr: Expression, trueExpr: Expression, falseExpr: Expression):
        self.condExpr = condExpr
        self.trueExpr = trueExpr
        self.falseExpr = falseExpr

        super().__init__()

    def evaluate(self, env: Env) -> Tuple[Optional[Expression], Env]:
        (cond, _) = self.condExpr.evaluate(env.makeChild())
        if not isinstance(cond, bool):
            raise Exception("Conditional expression wasn't a boolean")

        if cond :
            return self.trueExpr.evaluate(env.makeChild())
        else:
            return self.falseExpr.evaluate(env.makeChild())

    def __str__(self) -> str:
        return f"(if {self.condExpr} {self.trueExpr} {self.falseExpr})"

class Name(Expression):
    def __init__(self, name: str):
        super().__init__()
        self.name = name

    def evaluate(self, env: Env) -> Tuple[Optional[Expression], Env]:
        return (env.get(self.name), env)

    def inferType(self, env: Env):
        existingType= super().inferType(env)
        if existingType is not None:
            return existingType

        judgedType = env.get_judgement(self.name)
        if judgedType:
            self.annotation = judgedType
            return judgedType

        (val, _) = self.evaluate(env)
        print(f"Value of {self} is {val}")
        if val is None:
            raise Exception("Can't infer type of unbound variable")
        return val.inferType(env)

    def checkType(self, annotatedType, env: Env) -> bool:
        return self.inferType(env) == annotatedType

    def __str__(self) -> str:
        return f"@{self.name}"


class Define(Expression):
    def __init__(self, name: str, expr: Expression):
        self.name = name
        self.expr = expr

        super().__init__()

    def evaluate(self, env: Env) -> Tuple[Optional[Expression], Env]:
        env.set(self.name, self.expr)
        return (None, env)

    def __str__(self) -> str:
        return f"(define {self.name} {self.expr})"



class Lambda(Expression):
    def __init__(self, args: List[str], body: Expression):
        super().__init__()

        self.args = args
        self.body = body


    def evaluate(self, env: Env) -> Tuple[Optional[Expression], Env]:
        self.captured_env = env

        def callable(*argExpr: List[Expression]) -> Optional[Expression]:
            bodyEnv = self.captured_env.makeChild()

            for name, arg in zip(self.args, argExpr):
                bodyEnv.set(name, arg)

            return self.body.evaluate(bodyEnv)[0]

        return (Value(callable, self.inferType(env)), env)

    def inferType(self, env: Env):
        print(f"Lambda, infertype")
        if len(self.args) == 0:
            return [self.body.inferType(env)]

    def checkType(self, annotatedType, env: Env):
        print(f"Lambda, check type")
        childEnv = env.makeChild()
        returnType = annotatedType.pop()

        for (argName, argType) in zip(self.args, annotatedType):
            childEnv.set_judgement(argName, argType)

        return self.body.checkType(childEnv, returnType)

        # return self.inferType(env) == annotatedType


    def __str__(self) -> str:
        return f"(lambda ({' '.join(self.args)}) {self.body})"

class Call(Expression):
    def __init__(self, fnExpr: Expression, args: List[Expression]):
        self.fnExpr = fnExpr
        self.args = args

        super().__init__()

    def evaluate(self, env:Env) -> Tuple[Optional[Expression], Env]:
        fn = self.fnExpr
        print(fn)
        while not isinstance(fn, Value):
            print("hi")
            print(fn)
            (fn, _) = fn.evaluate(env.makeChild())
            assert fn is not None, f"In {self}, the function resolved to None"

        assert isinstance(fn, Value), f"Attempt to call non-value {fn}"
        assert callable(fn.value), f"Although call is a value, it's not a function: {fn}"

        evaluatedArgs = [a.evaluate(env.makeChild())[0] for a in self.args]
        return (fn.value(*evaluatedArgs), env)

    def __str__(self):
        return f"({self.fnExpr} {' '.join(str(a) for a in self.args)})"

class Judgement(Expression):
    def __init__(self, expr: Expression, typ: Expression):
        self.expr = expr
        self.judgement = typ

    def evaluate(self, env:Env) -> Tuple[Expression, Env]:

        if isinstance(self.expr, Name):
            name = self.expr.name
            env.set_judgement(name, self)
            if env.has(name):
                return (Value(self.verify(env)), env)
            else:
                return (Value("judgement recorded"), env)

        return (Value(self.verify(env)), env)

    def verify(self, env:Env) -> bool:
        print(f"Verifying {self.expr} with judgement {self.judgement}")

        (evaluatedType, _) = self.judgement.evaluate(env)
        print(f"Evaluated type for {self.judgement} is {evaluatedType}")

        print(f"Checking type of {self.expr}")
        return self.expr.checkType(evaluatedType, env)
        inferedType = self.expr.inferType(env)
        print(f"Infered type for {self.expr} is {inferedType}")

        return inferedType == evaluatedType

    def __str__(self):
        return f"(judge {self.expr} {self.judgement})"




def check_judgement(value, raw_judgement, env):
    print(f"Evaluating raw judgement {raw_judgement}")
    judgement = eval_val(raw_judgement, env, "J")
    print(f"Checking {value} with judgement {judgement}")

    if judgement == "Int" and (isinstance(value, int) or isinstance(value, float)):
        return True

    if judgement == "Str" and isinstance(value, str):
        return True

    if isinstance(judgement, list):
        print(f"judgement is a list")
        res_type = judgement[-1]



    print("TYPECHECK FAILED")
    return False


default_env = Env(bindings = {
    "+" : Value(add),
    "-" : Value(sub),
    "*" : Value(mul),
    "<=": Value(lte),
    "<": Value(lt),
    "=": Value(eq),
    "Int": Value("Int", "Type"),
    "Str": Value("Str", "Type"),
    "Bool": Value("Bool", "Type"),
    "Type": Value("Type", "Type"),
    "->": Value(arrow_type)
    })

default_env.set_axiom("+", ["->", "Int", "Int", "Int"])
default_env.set_axiom("*", ["->", "Int", "Int", "Int"])
default_env.set_axiom("Int", "Type")
default_env.set_axiom("Str", "Type")


def tokensToExpression(tokens) -> Expression:
    if not isinstance(tokens, list):
        return singleton(tokens)

    if len(tokens) == 0:
        raise Exception("Empty Expression???")

    first_token = tokens.pop(0)
    if first_token == "judge":
        [expr_tokens, judgement_tokens] = tokens
        expr_expr = tokensToExpression(expr_tokens)
        judgement_expr = tokensToExpression(judgement_tokens)
        return Judgement(expr=expr_expr, typ=judgement_expr)

    if first_token == "define":
        [name_token, expr_tokens] = tokens
        expr_tokens = tokensToExpression(expr_tokens)

        return Define(name = name_token, expr = expr_tokens)

    if first_token == "lambda":
        [arg_tokens, body_tokens] = tokens

        body_expr = tokensToExpression(body_tokens)

        return Lambda(args=arg_tokens, body=body_expr)

    if first_token == "if":
        [cond_tokens, true_tokens, false_tokens] = tokens
        cond_expr = tokensToExpression(cond_tokens)
        true_expr = tokensToExpression(true_tokens)
        false_expr = tokensToExpression(false_tokens)

        return IfStatement(condExpr=cond_expr, trueExpr=true_expr, falseExpr=false_expr)

    if first_token == "defun":
        [[name, *argnames], body] = tokens
        body_expr = tokensToExpression(body)
        return Define(name = name, expr = Lambda(args=argnames, body=body_expr))

    return Call(tokensToExpression(first_token), [tokensToExpression(t) for t in tokens])
    


def singleton(token: str) -> Expression:
    try:
        num = int(token)
        return Value(num)
    except:
        pass

    if isinstance(token, str):
        if token.startswith("'"):
            return Value(token)
        else:
            return Name(token)

    if isinstance(token, Expression):
        return token

    return Value(token)

def makeNextExpression(tokens: List[str]):
    current_expr = []
    while len(tokens) > 0:
        t = tokens.pop(0)

        if t == "(":
            t, tokens = makeNextExpression(tokens)
        elif t == ")":
            return (current_expr, tokens)

        current_expr.append(t)

    return (current_expr, tokens)


def parse(code_string: str) -> List[Expression]:
    special_chars = ["(", ")"]

    lines = [l.split("--", 1)[0] for l in code_string.splitlines()]

    code_string = "\n".join(lines)

    for s in special_chars:
        code_string = code_string.replace(s, f" {s} ")
    tokens = [t for t in code_string.split() if len(t) > 0]

    exprs_str, _ = makeNextExpression(tokens)

    expressions = []
    for single_expr_tokens in exprs_str:
        expr = tokensToExpression(single_expr_tokens) 

        expressions.append(expr)
    return  expressions




def main() -> None:
    parsed: List[Expression] = parse(test_string)
    env: Env = default_env

    for expr in parsed:
        print(f"> {expr}")
        (res, env) = expr.evaluate(env)
        if res is not None:
            print(res)
        print()

    while True:
        entry = input("> ")
        if entry == "exit":
            break

        exprs = parse(entry)
        for expr in exprs:
            (res, env) = expr.evaluate(env)
            if res is not None:
                print(res)


if __name__ == "__main__":
    main()
