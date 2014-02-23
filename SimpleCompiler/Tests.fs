module Tests
    open NUnit.Framework
    let idFuncSource = SourceLang.Lambda("x", SourceLang.Bool, SourceLang.Variable "x")

    module SourceTests =
        open SourceLang
        
        [<Test>]
        let testTypeOf() =
            Assert.AreEqual(Bool, typeOf Map.empty True)
            Assert.AreEqual(Product([Bool; Bool]), typeOf Map.empty (Tuple [True; False]))
            Assert.AreEqual(Function(Bool, Bool), typeOf Map.empty <| idFuncSource)
            
    module ConversionTests =
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
                                convertTerm idFuncSource, "ID function closure conversion")
            