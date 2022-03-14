# LLVMMyPass
My toy llvm passes
# passes
- Flatten.cpp 普通的控制流平坦化
- MyFlatten.cpp 使用区间判断，多个预分发块的控制流平坦化
- ConstantReplace.cpp 使用全局变量的常量混淆
- ConstantReplace2.cpp 使用局部变量的常量混淆
- VMFlatten.cpp 将平坦化以虚拟机的形式组织，控制流关系在opcode中
- VariableRotation.cpp 变量轮转混淆
- DataObfusactor.cpp 数据流混淆，加入大量垃圾代码，混淆变量之间关系
- BogusControlFlow 虚假控制流，但是是随机生成的表达式
# usage
目前没有集成到llvm项目中去，可以编译成so玩玩
```
clang `llvm-config --cxxflags` -Wl,-znodelete -fno-rtti -fPIC -shared VarObfu.cpp -o Var.so `llvm-config --ldflags`

clang -S -emit-llvm test.cpp -o test.ll

opt -load Var.so -var test.ll -S -o test_out.ll

llvm-as test_out.ll

clang test_out.ll -o test
```
