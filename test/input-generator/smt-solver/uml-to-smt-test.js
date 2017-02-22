const testee = require('../../../input-generator/smt-solver/uml-to-smt/index.js');

describe('UML-To-SMT', function () {
	it('should handle classes with both no variables or methods', function () {
		const fixture = {
			Test: {
				name: 'Test',
				variables: {},
				methods: {}
			}
		};
		const result = testee(fixture);

		expect(result).to.have.key('Test');
		expect(result.Test).to.include.keys('name', 'smtCommands');
		expect(result.Test.smtCommands).to.be.instanceOf(Array).and.have.length(0);
	});

	it('should handle classes with no variables', function () {
		const fixture = {
			Test: {
				name: 'Test',
				methods: {
					Foo: {
						name: 'Foo',
						visibility: 'Public',
						type: 'Integer',
						arguments: {
							a: 'Integer',
							b: 'Integer'
						},
						preconditions: [
							{
								comparison: 'Equal',
								arguments: [
									'a',
									0
								],
								id: '00000000-0000-0000-0000-000000000000'
							}
						],
						postconditions: [
							{
								comparison: 'GreaterThan',
								arguments: [
									'result',
									'a'
								],
								id: '00000000-0000-0000-0000-000000000001'
							}
						]
					}
				}
			}
		};
		const result = testee(fixture);

		expect(result).to.have.key('Test');
		expect(result.Test).to.include.keys('name', 'smtCommands');
		expect(result.Test.smtCommands).to.be.instanceOf(Array).and.have.length(1);
		expect(result.Test.smtCommands[0]).to.have.keys('name', 'commands');
		expect(result.Test.smtCommands[0].name).to.equal('Foo');
		expect(result.Test.smtCommands[0].commands).to.be.instanceOf(Array);
	});

	it('should handle classes with no methods', function () {
		const fixture = {
			Test: {
				name: 'Test',
				variables: {
					'Foo': {
						name: 'Foo',
						visibility: 'Public',
						type: 'Integer'
					}
				},
				methods: {}
			}
		};
		const result = testee(fixture);

		expect(result).to.have.key('Test');
		expect(result.Test).to.include.keys('name', 'smtCommands');
		expect(result.Test.smtCommands).to.be.instanceOf(Array).and.have.length(0);
	});

	it('should handle methods with no arguments');
	it('should handle methods with no preconditions');
	it('should handle methods with no postconditions');
	it('should handle methods with no arguments but preconditions on variables');
	it('should handle methods with no arguments but postconditions on variables');

	it('should handle multiple methods in a single class');
	it('should handle multiple classes');
	it('should handle multiple classes with multiple methods');

	describe('Assertions', function () {
		it('should make assertions on Equalities', function () {
			const fixture = {
				Test: {
					name: 'Test',
					methods: {
						Foo: {
							name: 'Foo',
							visibility: 'Public',
							type: 'Integer',
							arguments: {
								a: 'Integer',
								b: 'Integer'
							},
							preconditions: [
								{
									comparison: 'Equal',
									arguments: [
										'a',
										0
									],
									id: '00000000-0000-0000-0000-000000000000'
								}
							],
							postconditions: []
						}
					}
				}
			};
			const result = testee(fixture);

			expect(result).to.have.key('Test');
			expect(result.Test).to.have.keys('name', 'smtCommands');
			expect(result.Test.smtCommands).to.be.instanceOf(Array).and.have.length(1);
			expect(result.Test.smtCommands[0]).to.have.keys('name', 'commands');
			expect(result.Test.smtCommands[0].commands).to.be.instanceOf(Array);

			const commands = result.Test.smtCommands[0].commands;

			expect(commands[5]).to.include('(assert (= a 0))');
		});

		it('should make assertions on inverted equalities', function () {
			const fixture = {
				Test: {
					name: 'Test',
					methods: {
						Foo: {
							name: 'Foo',
							visibility: 'Public',
							type: 'Integer',
							arguments: {
								a: 'Integer',
								b: 'Integer'
							},
							preconditions: [
								{
									comparison: 'Equal',
									arguments: [
										'a',
										0
									],
									inverted: true,
									id: '00000000-0000-0000-0000-000000000000'
								}
							],
							postconditions: []
						}
					}
				}
			};
			const result = testee(fixture);

			expect(result).to.have.key('Test');
			expect(result.Test).to.have.keys('name', 'smtCommands');
			expect(result.Test.smtCommands).to.be.instanceOf(Array).and.have.length(1);
			expect(result.Test.smtCommands[0]).to.have.keys('name', 'commands');
			expect(result.Test.smtCommands[0].name).to.be.a('string').and.equal('Foo');
			expect(result.Test.smtCommands[0].commands).to.be.instanceOf(Array);

			const commands = result.Test.smtCommands[0].commands;

			expect(commands[5]).to.include('(assert (not (= a 0)))');
		});

		it('should error on making inverted assertions that are not allowed to be inverted');
	});

	describe('Types', function () {
		it('should convert type "Integer" to "Int"', function () {
			const fixture = {
				Test: {
					name: 'Test',
					methods: {
						Foo: {
							name: 'Foo',
							visibility: 'Public',
							type: 'Integer',
							arguments: {
								a: 'Integer',
								b: 'Integer'
							},
							preconditions: [
								{
									comparison: 'Equal',
									arguments: [
										'a',
										0
									],
									inverted: true,
									id: '00000000-0000-0000-0000-000000000000'
								}
							],
							postconditions: []
						}
					}
				}
			};
			const result = testee(fixture);
			const commands = result.Test.smtCommands[0].commands.join('\n');

			expect(commands).to.not.contain('Integer');
			expect(commands).to.contain('Int');
		});

		it('should convert type "Float" to "Real"', function () {
			const fixture = {
				Test: {
					name: 'Test',
					methods: {
						Foo: {
							name: 'Foo',
							visibility: 'Public',
							type: 'Float',
							arguments: {
								a: 'Float',
								b: 'Float'
							},
							preconditions: [
								{
									comparison: 'Equal',
									arguments: [
										'a',
										0
									],
									inverted: true,
									id: '00000000-0000-0000-0000-000000000000'
								}
							],
							postconditions: []
						}
					}
				}
			};
			const result = testee(fixture);
			const commands = result.Test.smtCommands[0].commands.join('\n');

			expect(commands).to.not.contain('Float');
			expect(commands).to.contain('Real');
		});

		it('should convert type "Double" to "Real"', function () {
			const fixture = {
				Test: {
					name: 'Test',
					methods: {
						Foo: {
							name: 'Foo',
							visibility: 'Public',
							type: 'Double',
							arguments: {
								a: 'Double',
								b: 'Double'
							},
							preconditions: [
								{
									comparison: 'Equal',
									arguments: [
										'a',
										0
									],
									inverted: true,
									id: '00000000-0000-0000-0000-000000000000'
								}
							],
							postconditions: []
						}
					}
				}
			};
			const result = testee(fixture);
			const commands = result.Test.smtCommands[0].commands.join('\n');

			expect(commands).to.not.contain('Double');
			expect(commands).to.contain('Real');
		});

		it('should convert type "Boolean" to "Bool"', function () {
			const fixture = {
				Test: {
					name: 'Test',
					methods: {
						Foo: {
							name: 'Foo',
							visibility: 'Public',
							type: 'Boolean',
							arguments: {
								a: 'Boolean',
								b: 'Boolean'
							},
							preconditions: [
								{
									comparison: 'Equal',
									arguments: [
										'a',
										true
									],
									inverted: true,
									id: '00000000-0000-0000-0000-000000000000'
								}
							],
							postconditions: []
						}
					}
				}
			};
			const result = testee(fixture);
			const commands = result.Test.smtCommands[0].commands.join('\n');

			expect(commands).to.not.contain('Boolean');
			expect(commands).to.contain('Bool');
		});
	});

	describe('Functions', function () {
		it('should generate a value for the execution of a function in precondition', function () {
			const fixture = {
				Test: {
					name: 'Test',
					methods: {
						Foo: {
							name: 'Foo',
							visibility: 'Public',
							type: 'Integer',
							arguments: {
								a: 'Integer',
								b: 'Integer'
							},
							preconditions: [
								{
									comparison: 'Equal',
									arguments: [
										{
											label: 'FunctionCall',
											type: 'Integer',
											name: 'Bar',
											arguments: [
												{
													type: 'Integer',
													value: 5
												}
											]
										},
										0
									],
									id: '00000000-0000-0000-0000-000000000000'
								}
							],
							postconditions: []
						},
						Bar: {
							name: 'Bar',
							visibility: 'Public',
							type: 'Integer',
							arguments: {
								a: 'Integer'
							},
							preconditions: [],
							postconditions: []
						}
					}
				}
			};
			const result = testee(fixture);

			expect(result).to.have.keys('Test');
			expect(result.Test).to.have.keys('name', 'smtCommands');
			expect(result.Test.smtCommands).to.be.instanceOf(Array).and.have.length(2);
			expect(result.Test.smtCommands[0]).to.have.keys('name', 'commands');
			expect(result.Test.smtCommands[0].name).to.be.a('string').and.equal('Foo');
			expect(result.Test.smtCommands[0].commands).to.be.instanceOf(Array);

			const commands = result.Test.smtCommands[0].commands;

			console.log(commands);
			expect(commands[5]).to.equal('(declare-fun Bar (Int) Int)');
			expect(commands[6]).to.equal('(assert (= (Bar 5) 0))');
			expect(commands[9]).to.contain('(get-value (a b (Bar 5)))');

			expect(result.Test.smtCommands[1]).to.have.keys('name', 'commands');
			expect(result.Test.smtCommands[1].name).to.be.a('string').and.equal('Bar');
			expect(result.Test.smtCommands[1].commands).to.be.instanceOf(Array);
		});
	});

	describe('Optional Preconditions', function () {
		it('should work with no optional preconditions', function () {
			const fixture = {
				Test: {
					name: 'Test',
					methods: {
						Foo: {
							name: 'Foo',
							visibility: 'Public',
							type: 'Integer',
							arguments: {
								a: 'Integer'
							},
							preconditions: [
								{
									comparison: 'GreaterThanOrEqual',
									arguments: [
										'a',
										0
									],
									id: '00000000-0000-0000-0000-000000000000'
								},
								{
									comparison: 'LessThanOrEqual',
									arguments: [
										'a',
										10
									],
									id: '00000000-0000-0000-0000-000000000000'
								}
							],
							postconditions: []
						}
					}
				}
			};
			const result = testee(fixture);
			const commands = result.Test.smtCommands[0].commands;

			expect(result).to.have.key('Test');
			expect(result.Test).to.have.keys('name', 'smtCommands');
			expect(result.Test.smtCommands).to.be.instanceOf(Array).and.have.length(1);
			expect(result.Test.smtCommands[0]).to.have.keys('name', 'commands');

			expect(commands).to.be.instanceOf(Array);
			expect(commands).to.contain('(assert (>= a 0))');
			expect(commands).to.contain('(assert (<= a 10))');
			expect(commands).to.contain('(assert (not (>= a 0)))');
			expect(commands).to.contain('(assert (not (<= a 10)))');
		});

		it('should make assertions on additional preconditions', function () {
			const fixture = {
				Test: {
					name: 'Test',
					methods: {
						Foo: {
							name: 'Foo',
							visibility: 'Public',
							type: 'Integer',
							arguments: {
								a: 'Integer'
							},
							preconditions: [
								{
									comparison: 'GreaterThanOrEqual',
									arguments: [
										'a',
										0
									],
									id: '00000000-0000-0000-0000-000000000000'
								},
								{
									comparison: 'LessThanOrEqual',
									arguments: [
										'a',
										10
									],
									id: '00000000-0000-0000-0000-000000000001'
								}
							],
							optionalPreconditions: [
								{
									comparison: 'GreaterThanOrEqual',
									arguments: [
										'a',
										6
									],
									id: '00000000-0000-0000-0000-000000000002'
								}
							],
							postconditions: []
						}
					}
				}
			};
			const result = testee(fixture);
			const commands = result.Test.smtCommands[0].commands;

			expect(commands).to.contain('(assert (>= a 6))');
			expect(commands).to.contain('(assert (not (>= a 6)))');
		});
	});
});
