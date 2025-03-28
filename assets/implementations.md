3.28
1. verifier.success 里面的判断roundOne的逻辑拿出来，放在调用success的地方，而不是进入后再判断。这样的好处是，我如果不进入，那我相关的string就不用计算出来。
   1. 实现方式：分离success的逻辑：一个是true，一个是msg
2. 