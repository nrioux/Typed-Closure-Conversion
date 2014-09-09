module Tests
    open NUnit.Framework
    let idFuncSource = SourceLang.Lambda(SourceLang.Bool, SourceLang.BoundVar 0u)

    module SourceFunctions =
        open SourceLang
        let notFunc = Lambda(Bool, If(BoundVar(0u), False, True))
        let applyFunc = Lambda(Function(Bool, Bool),
                                    Lambda(Bool,
                                            Application(BoundVar 1u, BoundVar 0u)))
        let idBoolBool = Lambda(Function(Bool, Bool), BoundVar 0u)
        let firstBool = Lambda(Bool, Lambda(Bool, BoundVar 1u))

    module SourceTests =
        open SourceLang
        open SourceFunctions
        
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
            Assert.AreEqual(notFunc, eval notFunc)
            Assert.AreEqual(True, eval <| Application(notFunc, False))
            Assert.AreEqual(False, eval <| Application(notFunc, True))
            Assert.AreEqual(True, eval <| Application (Application(applyFunc, notFunc), False))
            
    module TargetTests =
        open TargetLang
        open System.Diagnostics

        let notFunc = LambdaTerm(Bool, If(BoundVar 0u, False, True))
        let applyFunc = LambdaMulti [Function(Bool, Bool); Bool] <| ApplicationTerm(BoundVar 1u, BoundVar 0u)
        let applyFuncNested = LambdaTerm(Function(Bool, Bool), 
                                          LambdaTerm(Bool, ApplicationTerm(BoundVar 1u, BoundVar 0u)))
        let genericIdFunc = LambdaType <| LambdaTerm(BoundTypeVar 0u, BoundVar 0u)

        [<Test>]
        let testOpen() =
            Assert.AreEqual(openTerm False (If(BoundVar 0u, False, True)), If(False, False, True))

        [<Test>]
        let testEval() =
            Assert.AreEqual(True, eval True, "True")
            Assert.AreEqual(Tuple([True; False]), eval <| Tuple([True; False]))
            Assert.AreEqual(False, eval <| Projection(1, Tuple([True; False])))
            Assert.AreEqual(notFunc, eval notFunc)
            Assert.AreEqual(True, eval <| If(False, False, True))
            Assert.AreEqual(True, eval <| ApplicationTerm(notFunc, False))
            Assert.AreEqual(True, eval <| ApplicationMulti applyFunc [notFunc; False],
                            "applyFunc")
            Assert.AreEqual(True, eval <| ApplicationTerm(ApplicationType(genericIdFunc, Bool), True))
            let pack = Pack(Bool, True, BoundTypeVar 0u)
            Assert.AreEqual(pack, eval pack)

        [<Test>]
        let testTypeChecker() =
            Assert.AreEqual(Bool, getType True)
            Assert.AreEqual(Bool, getType <| Projection(1, Tuple([False; False; True])))
            Assert.AreEqual(Product([Bool; Bool]), getType <| Tuple([True; False]))
            Assert.AreEqual(Function(Bool, Bool), getType <| ApplicationType(genericIdFunc, Bool))
            Assert.AreEqual(Function(Bool, Bool), getType notFunc)
            Assert.AreEqual(Existential(Bool), getType <| Pack(Bool, True, Bool))
            Assert.AreEqual(Existential(BoundTypeVar 0u), getType <| Pack(Bool, True, BoundTypeVar 0u))

        [<Test>]
        let testEvalCurry() =
            Assert.AreEqual(True, eval <| ApplicationTerm(ApplicationTerm(applyFunc, notFunc), False),
                            "applyFunc curried")

        [<Test>]
        let testEvalNestedCurry() =
            Assert.AreEqual(True, eval <| ApplicationTerm(ApplicationTerm(applyFuncNested, 
                                                            notFunc), False),
                            "applyFuncNested")

    module ConversionTests =
        open ClosureConversion
        open System.Diagnostics

        let idFuncTargetType = TargetLang.Existential(
                                   TargetLang.Product([(TargetLang.FunctionMulti [TargetLang.BoundTypeVar 0u;
                                                                 TargetLang.Bool]
                                                              TargetLang.Bool);
                                   TargetLang.BoundTypeVar 0u]))

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
            let x = SourceLang.genId ()
            let y = SourceLang.genId ()
            Assert.AreEqual([x], SourceLang.freeVariables <| SourceLang.FreeVar x)
            
            Assert.AreEqual(Set.ofList [x; y], Set.ofList
                                            (SourceLang.freeVariables <|
                                                SourceLang.Tuple([SourceLang.FreeVar x; 
                                                                  SourceLang.FreeVar y])))

        [<Test>]
        let testClosureConversion() =
            Assert.AreEqual(TargetLang.True, convertTerm SourceLang.True)
            Assert.AreEqual(TargetLang.Tuple([TargetLang.True; TargetLang.False]),
                            convertTerm <| SourceLang.Tuple([SourceLang.True; SourceLang.False]))
            let env = TargetLang.Tuple([])
            let tenv = TargetLang.Product([])
            let body = TargetLang.LambdaType(TargetLang.LambdaMulti [tenv; TargetLang.Bool]
                                                                    <| TargetLang.BoundVar 0u)
            match idFuncTargetType with
            | TargetLang.Existential(tau) ->
                let expected = TargetLang.Pack(tenv, TargetLang.Tuple([TargetLang.ApplicationType(body, tenv); env]), tau)
                let actual = convertTerm idFuncSource
                Assert.AreEqual(expected, actual, "ID function closure conversion")
       
        [<Test>]
        let testFuncs() =
            let test = SourceLang.Application(SourceFunctions.notFunc, SourceLang.True)
            Assert.AreEqual(TargetLang.False, TargetLang.eval <| convertTerm test)
            
            let test = SourceLang.Application(SourceLang.Application(SourceFunctions.idBoolBool, 
                                                                        SourceFunctions.notFunc),
                                                SourceLang.True)
            let test' = convertTerm test
            Assert.AreEqual(TargetLang.False, TargetLang.eval test')

            
        let checkConversionEquiv e =
            let a = convertTerm <| SourceLang.eval e
            let at = TargetLang.getType a
            let b = convertTerm e
            let bt = TargetLang.getType b
            Assert.AreEqual(at, bt, "Conversion type preservation")

            let a' = TargetLang.eval a
            let b' = TargetLang.eval b
            
            Assert.AreEqual(bt, TargetLang.getType b', "Eval type preservation")
            Assert.AreEqual(a', b', "Conversion equivalence")

        [<Test>]
        let testConversionEquivalence() =
            checkConversionEquiv <| SourceFunctions.idBoolBool
            checkConversionEquiv <| SourceLang.Application(SourceFunctions.notFunc, SourceLang.True)
            checkConversionEquiv <| SourceLang.Application(SourceLang.Application(SourceFunctions.idBoolBool, 
                                                            SourceFunctions.notFunc), SourceLang.True)
            let app = SourceLang.Application(
                          SourceLang.Application(
                              SourceFunctions.firstBool,
                              SourceLang.True),
                          SourceLang.False)
            checkConversionEquiv app

            let test = SourceLang.Application(SourceLang.Application(SourceFunctions.applyFunc,
                                                SourceFunctions.idBoolBool), SourceLang.True)
            checkConversionEquiv test