Class {
	#name : #PPTASTCheckingTestGenerator,
	#superclass : #Object,
	#category : #'PetitParserTooling-TestSupport'
}

{ #category : #'as yet unclassified' }
PPTASTCheckingTestGenerator >> ensureTestClassFor: aParserClass inPackage: parserTestClassPackage [
	| testParserClassName testParserClass |
	testParserClassName := (aParserClass name , #Test) asSymbol.
	testParserClass := [ self class environment at: testParserClassName ]
		on: NotFound
		do: [ PP2CompositeNodeTest
				subclass: testParserClassName
				instanceVariableNames: ''
				classVariableNames: ''
				package: parserTestClassPackage ].
	(PCGMethodNode selector: #parserClass)
		bodyBlock: [ :body | body << aParserClass name asPCGGlobal returnIt ];
		protocol: #accessing;
		installOn: testParserClass.
	^ testParserClass
]

{ #category : #'as yet unclassified' }
PPTASTCheckingTestGenerator >> generateAllTestsFor: aParserClass inPackage: parserTestClassPackage fromTestClass: aTestClass [
	| tests testInstance testClass |
	testClass := self
		ensureTestClassFor: aParserClass
		inPackage: parserTestClassPackage.
	testInstance := testClass new setUp.
	tests := self getAllTestsAssertionsFrom: aTestClass.
	(tests groupedBy: [ :t | t arguments second value ])
		keysAndValuesDo: [ :ruleName :testsForRule | 
			testsForRule
				doWithIndex: [ :test :index | 
					| pcgStruct |
					[ pcgStruct := (PCGMethodNode
						selector: (#test , ruleName capitalized , index asString) asSymbol)
						bodyBlock: [ :body | 
							body
								<<
									(#self asPCGNode
										receiveMessage: #assert:equals:
										with: (PCGRealASTToPCGConverter visit: test)
										with:
											(self
												obtainPCGStoreOnFor:
													(testInstance
														perform: test selector
														with: test arguments first value
														with: test arguments second value))) ].
					[ pcgStruct installOn: testClass ]
						on: Error
						do: [  ] ]
						on: TestFailure
						do: [  ] ] ]
]

{ #category : #'as yet unclassified' }
PPTASTCheckingTestGenerator >> getAllTestsAssertionsFrom: aTestClass [
	| query tests |
	tests := OrderedCollection new.
	query := TreeQuery breadthFirst
		predicate:
			[ :n | n class = RBMessageNode and: [ n selector = #parse:rule: ] ]
				asTQPredicate;
		collectMatches.
	aTestClass methods
		select: #isTestMethod
		thenDo: [ :m | tests addAll: (query runOn: m ast childrenBlock: #children) ].
	^ tests
]

{ #category : #generation }
PPTASTCheckingTestGenerator >> obtainPCGStoreOnFor: aPWBASTNode [
	| cascade |
	[ ^ aPWBASTNode asPCG ]
		on: MessageNotUnderstood
		do: [  ].
	aPWBASTNode class = OrderedCollection
		ifTrue: [ ^ #OrderedCollection asPCGGlobal
				receiveMessage: #withAll:
				with:
					(PCGArrayNode
						statements: (aPWBASTNode collect: [ :e | self obtainPCGStoreOnFor: e ])) ].
	aPWBASTNode class = Array
		ifTrue: [ ^ PCGArrayNode
				statements: (aPWBASTNode collect: [ :e | self obtainPCGStoreOnFor: e ]) ].
	cascade := (aPWBASTNode class name asPCGGlobal receiveMessage: #new)
		asCascadeTarget.
	aPWBASTNode class instVarNames
		do: [ :instanceVariableName | 
			cascade
				receiveMessage: (instanceVariableName , ':') asSymbol
				with:
					(self obtainPCGStoreOnFor: (aPWBASTNode perform: instanceVariableName)) ].
	cascade receiveMessage: #yourself.
	^ cascade
]
