const chai = require('chai');
const expect = chai.expect;

const testee = require('../../input-generator/smt-solver/uml-to-smt/index.js');

describe('UML-To-SMT', () => {
	it('should assert Equalities', () => {
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
		expect(result.Test.smtCommands[0].name).to.be.a('string').and.equal('Foo');
		expect(result.Test.smtCommands[0].commands).to.include('(assert (= a 0))');
	});
});
