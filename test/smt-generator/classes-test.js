const chai = require('chai');
const expect = chai.expect;

const testee = require('../../src/smt-generator/util/smt-classes.js');
let TestClass;

describe('SMT Classes', () => {
	describe('Assertion', () => {
		before(() => {
			TestClass = testee.Assertion;
		});

		it('should error on empty input', () => {
			expect(() => {
				new TestClass();
			}).to.throw(Error);
		});

		it('should take a string input', () => {
			const obj = new TestClass('string');

			expect(obj.toString()).to.equal('(assert string)');
		});

		it('should take a SmtBooleanExpression', () => {
			const booleanExpression = testee.createBooleanExpression({
				comparison: '<',
				a: 'a',
				b: '0'
			});
			const obj = new TestClass(booleanExpression);

			expect(obj.toString()).to.equal('(assert (< a b))');
		});
	});
});
