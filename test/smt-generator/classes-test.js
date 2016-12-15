const chai = require('chai');
const expect = chai.expect;

const testee = require('../../src/smt-generator/util/smt-classes.js');
let TestClass;

describe('SMT Classes', () => {
	describe('Boolean Expression', () => {
		before(() => {
			TestClass = testee.BooleanExpression;
		});

		it('should error on empty input', () => {
			expect(() => {
				new TestClass();
			}).to.throw(Error);
		});

		it('should take a comparison and argument list');
		it('should take a comparison and argument list containing BooleanExpressions');
		it('should do a lookup to convert a comparison to SMT-LIB2 version');
		it('should change isInverted with setInverted');
		it('should represent SMT-LIB2 command differently if inverted');
	});

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

	describe('DeclareConst', () => {
		before(() => {
			TestClass = testee.DeclareConst;
		});

		it('should error on empty input', () => {
			expect(() => {
				new TestClass();
			}).to.throw(Error);
		});

		it('should error on an unknown type name');
		it('should take a name and type name');
	});

	describe('DeclareFunction', () => {
		before(() => {
			TestClass = testee.DeclareFunction;
		});

		it('should error on empty input', () => {
			expect(() => {
				new TestClass();
			}).to.throw(Error);
		});

		it('should error on an unknown type name');
		it('should error on unknown type names in arguments type list');
		it('should take a name and type name and arguments type list');
	});

	describe('FunctionCall', () => {
		before(() => {
			TestClass = testee.FunctionCall;
		});

		it('should error on empty input', () => {
			expect(() => {
				new TestClass();
			}).to.throw(Error);
		});

		it('should error on unknown function name');
		it('should take a name and arguments list');
	});

	describe('Echo', () => {
		before(() => {
			TestClass = testee.Echo;
		});

		it('should take an empty input');
		it('should take a string');
		it('should take a string with "double quotes"');
	});

	describe('GetValue', () => {
		before(() => {
			TestClass = testee.GetValue;
		});

		it('should error on empty input', () => {
			expect(() => {
				new TestClass();
			}).to.throw(Error);
		});

		it('should take an arguments list');
		it('should generate a check-sat before the get-value');
	});

	describe('Stack', () => {
		before(() => {
			TestClass = testee.GetValue;
		});

		it('should default to push on empty input');
		it('should take a string for mode');
		it('should error if string is not "push" or "pop"');
		it('should create correct SMT-LIB2 command depending on the mode');
	});
});
