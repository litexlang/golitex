# eval fn design

# eval_fn 在返回的时候，会检查

fn f(n Z) Z
know forall n Z: n % 3 = 1 => f(n) = n
know forall n Z: n % 3 = 2 => f(n) = n + 1
know forall n Z: n % 3 = 0 => f(n) = n + 2

# eval_fn 的意义是，计算出数值；计算出的这个数值，是需要一步步证明出来它是对的；比如 if n % 3 = 1的；情况中，要先证明 f(n) = n 是对的，然后才能返回 n；eval_fn 的返回值必须是可计算的，否则会报错。（可计算：一个数，或者四则运算，或者里面包含了定义好了eval_fn的函数。比如 g 定义好了eval_fn，同时这个eval_fn形式定义的g确实是处处等于 g(n) 的）
# 每当你定义了一个
eval_fn f(n):
    if n % 3 = 1:
        f(n) = n # 检查
        return n # 返回，并计算出数值

    n % 3 != 1 # 自动成立

    if n % 3 = 2:
        g(n) = n + 1 # 检查
        return n + 1 # 返回，并计算出数值

    n % 2 = 2

    if n % 3 = 0:
        g(n) = n + 2 # 检查
        return n + 2 # 返回，并计算出数值

fn g(n N_pos) Z
know forall n N_pos => g(n + 1) = g(n) + 1
know g(1) = 1

eval_fn g(n):
    if n = 1:
        return 1

    # 下面的环境里， n != 1 成立。可以用于证明条件
    n > 1 # 因为 N_pos 是正整数，所以 n 如果 n != 1，那么 n > 1

    return g(n - 1) + 1 # n - 1 是正整数，所以 n - 1 在 g 的定义域内，同时 g(n - 1) 是可计算的，所以合理。

