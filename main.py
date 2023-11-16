test_string = """

a: Int
a = 1

times: Int -> Int -> Int
times left right =
    left + right

r2: Int -> Int -> Int
r2 x y =
    let
        x2 = times x x
        y2 = times y y
    in
    add x2 y2

Bool: Type
Bool =
    True:Bool | False:Bool

Maybe: Type -> Type
Maybe t =
    Empty:(Maybe t)
    | Something:(t -> Maybe t) t 

"""

print(test_string)


def main():
    print(test_string)

if __name__ == "__main__":
    main()
