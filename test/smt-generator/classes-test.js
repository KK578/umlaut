const chai = require('chai');
const expect = chai.expect;

const testee = require('../../src/smt-generator/util/smt-classes.js');
let TestClass;

describe('SMT Classes', () => {
	describe('BooleanExpression', () => {
		before(() => {
			TestClass = testee.BooleanExpression;
		});

		it('should error on empty input', () => {
			expect(() => {
				new TestClass();
			}).to.throw(Error);
		});

		it('should take a comparison and argument list', () => {
			const obj = new TestClass('>', ['a', 'b']);

			// Default inversion is false
			expect(obj.isInverted).to.not.be.true;
			expect(obj.toString()).to.equal('(> a b)');
		});

		it('should take a comparison and argument list and boolean for inversion mode', () => {
			const obj = new TestClass('>', ['a', 'b'], true);

			expect(obj.isInverted).to.be.true;
			expect(obj.toString()).to.equal('(not (> a b))');
		});

		it('should change isInverted with setInverted', () => {
			const obj = new TestClass('>', ['a', 'b']);

			obj.setInverted(true);
			expect(obj.isInverted).to.be.true;
			obj.setInverted(false);
			expect(obj.isInverted).to.not.be.true;
		});

		it('should do a lookup to convert a comparison to SMT-LIB2 version', () => {
			const obj = new TestClass('==', ['a', '0']);

			expect(obj.toString()).to.equal('(= a 0)');
		});

		it('should handle comparator "!=" correctly as a SMT-LIB2 command', () => {
			const obj = new TestClass('!=', ['a', '0']);

			expect(obj.isInverted).to.be.true;
			expect(obj.toString()).to.equal('(not (= a 0))');
		});

		it('should take a comparison and argument list containing BooleanExpressions', () => {
			const obj = new TestClass('=', ['a', 'b']);
			const obj2 = new TestClass('=', ['a', '0']);
			const joinedObj = new TestClass('=', [obj, obj2]);

			expect(obj.toString()).to.equal('(= a b)');
			expect(obj2.toString()).to.equal('(= a 0)');
			expect(joinedObj.toString()).to.equal('(= (= a b) (= a 0))');
		});
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

		it('should take a BooleanExpression', () => {
			const booleanExpression = new testee.BooleanExpression('>', ['a', 'b']);
			const obj = new TestClass(booleanExpression);

			expect(obj.toString()).to.equal('(assert (> a b))');
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

		it('should take a name and type name', () => {
			const obj = new TestClass('a', 'Int');

			expect(obj.toString()).to.equal('(declare-const a Int)');
		});
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

		it('should take a name and type name and arguments type list', () => {
			const obj = new TestClass('foo', 'Int', ['Int', 'Int']);

			expect(obj.toString()).to.equal('(declare-fun a (Int Int) Int)');
		});
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

		it('should take just a name', () => {
			const obj = new TestClass('foo');

			expect(obj.toString()).to.equal('(foo)');
		});

		it('should take a name and arguments list', () => {
			const obj = new TestClass('foo', ['a', 'b']);

			expect(obj.toString()).to.equal('(foo a b)');
		});
	});

	describe('Echo', () => {
		before(() => {
			TestClass = testee.Echo;
		});

		it('should take an empty input', () => {
			const obj = new TestClass();

			expect(obj.toString()).to.equal('(echo "")');
		});

		it('should take a string', () => {
			const obj = new TestClass('foo bar');

			expect(obj.toString()).to.equal('(echo "foo bar")');
		});

		it('should take a string with "double quotes"', () => {
			const obj = new TestClass('some "foo" and "bar"');

			expect(obj.toString()).to.equal('(echo "some ""foo"" and ""bar""")');
		});

		it('could error on double quote, due to z3 not supporting this properly');
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

		it('should take an arguments list with one object', () => {
			const obj = new TestClass(['a']);

			expect(obj.toString()).to.match(/\(get-value \(a\)\)/);
		});

		it('should generate a check-sat before the get-value', () => {
			const obj = new TestClass(['a']);

			expect(obj.toString()).to.match(/^\(check-sat\)/);
		});

		it('should take an arguments list', () => {
			const obj = new TestClass(['a', 'b']);

			expect(obj.toString()).to.match(/\(get-value \(a b\)\)/);
		});
	});

	describe('StackModifier', () => {
		before(() => {
			TestClass = testee.StackModifier;
		});

		it('should default to push on empty input', () => {
			const obj = new TestClass();

			expect(obj.toString()).equal('(push)');
		});

		it('should take a string for mode', () => {
			const objPush = new TestClass('push');
			const objPop = new TestClass('pop');

			expect(objPush.toString()).equal('(push)');
			expect(objPop.toString()).equal('(pop)');
		});

		it('should error if string is not "push" or "pop"', () => {
			expect(() => {
				new TestClass('foo');
			}).to.throw(Error);
		});
	});
});
