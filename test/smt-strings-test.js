const expect = require('chai').expect;
const smtStrings = require('../util/smt-strings.js');

let testee;

describe('smt-strings', () => {
	before(() => {
		testee = new smtStrings();
	});

	describe('declareConst', () => {
		it('should declare constants', () => {
			const actual = testee.declareConst('a', 'Int');

			expect(actual).to.equal('(declare-const a Int)');
		});
	});

	describe('declareFunction', () => {
		it('should declare a function', () => {
			const actual = testee.declareFunction('Foo', 'a', 'Int');

			expect(actual).to.equal('(declare-fun Foo (a) Int)');
		});

		it('should declare a function from multiple arguments in string', () => {
			const actual = testee.declareFunction('Foo', 'a b c', 'Int');

			expect(actual).to.equal('(declare-fun Foo (a b c) Int)');
		});

		it('should declare a function from argument array', () => {
			const actual = testee.declareFunction('Foo', ['a', 'b', 'c'], 'Int');

			expect(actual).to.equal('(declare-fun Foo (a b c) Int)');
		});
	});

	describe('makeAssertion', () => {
		it('should make an assertion', () => {
			const actual = testee.makeAssertion('>=', 'a', 'b');

			expect(actual).to.equal('(assert (>= a b))');
		});

		it('should make an assertion with a function call', () => {
			const functionCall = testee.makeFunctionCall('Foo', 'a');
			const actual = testee.makeAssertion('>=', functionCall, 'b');

			expect(actual).to.equal('(assert (>= (Foo a) b))');
		});
	});

	describe('makeFunctionCall', () => {
		it('should make a function call', () => {
			const actual = testee.makeFunctionCall('Foo', 'a');

			expect(actual).to.equal('(Foo a)');
		});

		it('should make a function call from multiple arguments in string', () => {
			const actual = testee.makeFunctionCall('Foo', 'a b c');

			expect(actual).to.equal('(Foo a b c)');
		});

		it('should make a function call from argument array', () => {
			const actual = testee.makeFunctionCall('Foo', ['a', 'b', 'c']);

			expect(actual).to.equal('(Foo a b c)');
		});
	});

	describe('Simple Strings', () => {
		it('stackPush should return "(push)"', () => {
			const actual = testee.stackPush();

			expect(actual).to.equal('(push)');
		});

		it('stackPop should return "(pop)"', () => {
			const actual = testee.stackPop();

			expect(actual).to.equal('(pop)');
		});

		it('checkSat should return "(check-sat)"', () => {
			const actual = testee.checkSat();

			expect(actual).to.equal('(check-sat)');
		});

		it('getModel should return "(get-model)"', () => {
			const actual = testee.getModel();

			expect(actual).to.equal('(get-model)');
		});
	});
});
