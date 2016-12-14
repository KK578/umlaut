const chai = require('chai');
const expect = chai.expect;

const testee = require('../../src/smt-generator/util/smt-classes.js');

describe('SMT Classes', () => {
	describe('Assertion', () => {
		it('should error on empty input', () => {
			expect(testee.createAssertion).to.throw(Error);
		});

		it('should take a string input', () => {
			const obj = testee.createAssertion('string');

			expect(obj.toString()).to.equal('(assert string)');
		});

		it('should take a SmtBooleanExpression', () => {
			const booleanExpression = testee.createBooleanExpression({
				comparison: '<',
				a: 'a',
				b: '0'
			});
			const obj = testee.createAssertion(booleanExpression);

			expect(obj.toString()).to.equal('(assert (< a b))');
		});
	});
});
