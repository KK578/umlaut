const testee = require('../../../input-generator/smt-solver/uml-to-smt/index.js');

describe('UML-To-SMT', () => {
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
});
