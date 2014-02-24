module Tests
    open NUnit.Framework
    let idFuncSource = SourceLang.Lambda(0, SourceLang.Bool, SourceLang.Variable 0)

    module SourceTests =
        open SourceLang
        
        [<Test>]
        let testTypeOf() =
            Assert.AreEqual(Bool, typeOf Map.empty True)
            Assert.AreEqual(Product([Bool; Bool]), typeOf Map.empty (Tuple [True; False]))
            Assert.AreEqual(Function(Bool, Bool), typeOf Map.empty <| idFuncSource)

        [<Test>]
        let testEval() =
            Assert.AreEqual(True, eval True)
            Assert.AreEqual(idFuncSource, eval idFuncSource)
            Assert.AreEqual(False, eval <| Projection(1, Tuple([True; False])))
            let notFunc = Lambda(0, Bool, If(Variable 0, False, True))
            Assert.AreEqual(notFunc, eval notFunc)
            Assert.AreEqual(True, eval <| Application(notFunc, False))
            Assert.AreEqual(False, eval <| Application(notFunc, True))
            let applyFunc = Lambda(0, Bool,
                                    Lambda(1, SourceLang.Bool,
                                            Application(Variable 0, Variable 1)))
            Assert.AreEqual(True, eval <| Application (Application(applyFunc, notFunc), False))
            
    module TargetTests =
        open TargetLang

        let notFunc = Lambda(0, [Bool], If(Variable 0, False, True))
        let applyFunc = Lambda(0, [Function([0], [Bool], Bool); Bool], Application(Variable 1, [], [Variable 0]))
        let applyFuncNested = Lambda(0, [Function([0], [Bool], Bool)], 
                                          Lambda(0, [Bool], Application(Variable 1, [], [Variable 0])))

        [<Test>]
        let testEval() =
            Assert.AreEqual(True, eval True, "True")
            Assert.AreEqual(Tuple([True; False]), eval <| Tuple([True; False]))
            Assert.AreEqual(False, eval <| Projection(1, Tuple([True; False])))
            Assert.AreEqual(notFunc, eval notFunc)
            Assert.AreEqual(True, eval <| Application(notFunc, [], [False]))
            Assert.AreEqual(True, eval <| Application(applyFunc, [], [notFunc; False]),
                            "applyFunc")

        [<Test>]
        let testEvalCurry() =
            Assert.AreEqual(True, eval <| Application(Application(applyFunc, 
                                                            [], [notFunc]), [], [False]),
                            "applyFunc curried")

        [<Test>]
        let testEvalNestedCurry() =
            Assert.AreEqual(True, eval <| Application(Application(applyFuncNested, 
                                                            [], [notFunc]), [], [False]),
                            "applyFuncNested")
    
    (*module ConversionTests =
        open ClosureConversion

        let idFuncTargetType = TargetLang.Existential("A", TargetLang.Product([TargetLang.Function(List.empty, [TargetLang.TypeVariable("A"); 
                                                                                                                TargetLang.Bool], TargetLang.Bool);
                                                                                TargetLang.TypeVariable("A")]))

        [<Test>]
        let testTranslationType() =
            Assert.AreEqual(TargetLang.Bool, translationType SourceLang.Bool)
            Assert.AreEqual(idFuncTargetType, 
                            translationType <| SourceLang.Function(SourceLang.Bool, SourceLang.Bool))
            Assert.AreEqual(TargetLang.Product([TargetLang.Bool; TargetLang.Bool]), 
                            translationType <| SourceLang.Product([SourceLang.Bool; SourceLang.Bool]),
                            "Product translation type")

        [<Test>]
        let testFV() =
            Assert.AreEqual([], SourceLang.freeVariables SourceLang.True)
            Assert.AreEqual([], SourceLang.freeVariables idFuncSource)
            Assert.AreEqual(["x"], SourceLang.freeVariables <| SourceLang.Variable "x")
            Assert.AreEqual(["x"; "y"], SourceLang.freeVariables <|
                                            SourceLang.Tuple([SourceLang.Variable "x"; 
                                                                SourceLang.Variable "y"]))

        [<Test>]
        let testClosureConversion() =
            Assert.AreEqual(TargetLang.True, convertTerm SourceLang.True)
            Assert.AreEqual(TargetLang.Tuple([TargetLang.True; TargetLang.False]),
                            convertTerm <| SourceLang.Tuple([SourceLang.True; SourceLang.False]))
            let env = TargetLang.Tuple([])
            let tenv = TargetLang.Product([])
            let body = TargetLang.Lambda(["B"], Map.ofList ["env", TargetLang.TypeVariable "B"; "x", TargetLang.Bool], TargetLang.Variable "x")
            match idFuncTargetType with
            | TargetLang.Existential(alpha, tau) ->
                Assert.AreEqual(TargetLang.Pack(tenv, TargetLang.Tuple([TargetLang.Application(body, [tenv], []); env]), alpha, tau),
                                convertTerm idFuncSource, "ID function closure conversion")*)
            