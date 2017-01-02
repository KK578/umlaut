const testee = require('../../../input-generator/smt-solver/util/classes.js');
let TestClass;

describe('SMT Classes', function () {
	describe('BooleanExpression', function () {
		before(function () {
			TestClass = testee.BooleanExpression;
		});

		it('should error on empty input', function () {
			expect(() => {
				new TestClass();
			}).to.throw(Error);
		});

		it('should take a comparison and argument list', function () {
			const obj = new TestClass('>', ['a', 'b']);

			// Default inversion is false
			expect(obj.isInverted).to.not.be.true;
			expect(obj.toString()).to.equal('(> a b)');
		});

		it('should take a comparison and argument list and boolean for inversion mode', function () {
			const obj = new TestClass('>', ['a', 'b'], true);

			expect(obj.isInverted).to.be.true;
			expect(obj.toString()).to.equal('(not (> a b))');
		});

		it('should error if argument list is not an array', function () {
			expect(() => {
				new TestClass('>', 'a', 'b');
			}).to.throw(Error);
		});

		it('should error if comparison is not a valid SMT-LIB2 comparison', function () {
			expect(() => {
				new TestClass('==', ['a', '0']);
			}).to.throw(Error);
		});

		it('should change isInverted with setInverted', function () {
			const obj = new TestClass('>', ['a', 'b']);

			obj.setInverted(true);
			expect(obj.isInverted).to.be.true;
			obj.setInverted(false);
			expect(obj.isInverted).to.not.be.true;
		});

		it('should take a comparison and argument list containing BooleanExpressions', function () {
			const obj = new TestClass('=', ['a', 'b']);
			const obj2 = new TestClass('=', ['a', '0']);
			const joinedObj = new TestClass('=', [obj, obj2]);

			expect(obj.toString()).to.equal('(= a b)');
			expect(obj2.toString()).to.equal('(= a 0)');
			expect(joinedObj.toString()).to.equal('(= (= a b) (= a 0))');
		});
	});

	describe('Assertion', function () {
		before(function () {
			TestClass = testee.Assertion;
		});

		it('should error on empty input', function () {
			expect(() => {
				new TestClass();
			}).to.throw(Error);
		});

		it('should error on string input', function () {
			expect(() => {
				new TestClass('string');
			}).to.throw(Error);
		});

		it('should take a BooleanExpression', function () {
			const booleanExpression = new testee.BooleanExpression('>', ['a', 'b']);
			const obj = new TestClass(booleanExpression);

			expect(obj.toString()).to.equal('(assert (> a b))');
		});
	});

	describe('DeclareConst', function () {
		before(function () {
			TestClass = testee.DeclareConst;
		});

		it('should error on empty input', function () {
			expect(() => {
				new TestClass();
			}).to.throw(Error);
		});

		it('should error with just name', function () {
			expect(() => {
				new TestClass('a');
			}).to.throw(Error);
		});

		it('should take a name and type name', function () {
			const obj = new TestClass('a', 'Int');

			expect(obj.toString()).to.equal('(declare-const a Int)');
		});
	});

	describe('DeclareFunction', function () {
		before(function () {
			TestClass = testee.DeclareFunction;
		});

		it('should error on empty input', function () {
			expect(() => {
				new TestClass();
			}).to.throw(Error);
		});

		it('should error with just name', function () {
			expect(() => {
				new TestClass('a');
			}).to.throw(Error);
		});

		it('should error if argument list is not an array', function () {
			expect(() => {
				new TestClass('foo', 'Int', 'Int');
			}).to.throw(Error);
		});

		it('should take a name and type name and empty arguments type list', function () {
			const obj = new TestClass('foo', 'Int', []);

			expect(obj.toString()).to.equal('(declare-fun foo () Int)');
		});

		it('should take a name and type name and arguments type list', function () {
			const obj = new TestClass('foo', 'Int', ['Int', 'Int']);

			expect(obj.toString()).to.equal('(declare-fun foo (Int Int) Int)');
		});
	});

	describe('FunctionCall', function () {
		before(function () {
			TestClass = testee.FunctionCall;
		});

		it('should error on empty input', function () {
			expect(() => {
				new TestClass();
			}).to.throw(Error);
		});

		it('should take just a name', function () {
			const obj = new TestClass('foo');

			expect(obj.toString()).to.equal('(foo)');
		});

		it('should take a name and arguments list', function () {
			const obj = new TestClass('foo', ['a', 'b']);

			expect(obj.toString()).to.equal('(foo a b)');
		});
	});

	describe('Echo', function () {
		before(function () {
			TestClass = testee.Echo;
		});

		it('should take an empty input', function () {
			const obj = new TestClass();

			expect(obj.toString()).to.equal('(echo "")');
		});

		it('should take a string', function () {
			const obj = new TestClass('foo bar');

			expect(obj.toString()).to.equal('(echo "foo bar")');
		});

		it('should take a string with "double quotes"', function () {
			const obj = new TestClass('some "foo" and "bar"');

			expect(obj.toString()).to.equal('(echo "some ""foo"" and ""bar""")');
		});
	});

	describe('GetValue', function () {
		before(function () {
			TestClass = testee.GetValue;
		});

		it('should error on empty input', function () {
			expect(() => {
				new TestClass();
			}).to.throw(Error);
		});

		it('should take an arguments list with one object', function () {
			const obj = new TestClass(['a']);

			expect(obj.toString()).to.match(/\(get-value \(a\)\)/);
		});

		it('should generate a check-sat before the get-value', function () {
			const obj = new TestClass(['a']);

			expect(obj.toString()).to.match(/^\(check-sat\)/);
		});

		it('should take an arguments list', function () {
			const obj = new TestClass(['a', 'b']);

			expect(obj.toString()).to.match(/\(get-value \(a b\)\)/);
		});
	});

	describe('StackModifier', function () {
		before(function () {
			TestClass = testee.StackModifier;
		});

		it('should default to push on empty input', function () {
			const obj = new TestClass();

			expect(obj.toString()).equal('(push)');
		});

		it('should take a string for mode', function () {
			const objPush = new TestClass('push');
			const objPop = new TestClass('pop');

			expect(objPush.toString()).equal('(push)');
			expect(objPop.toString()).equal('(pop)');
		});

		it('should error if string is not "push" or "pop"', function () {
			expect(() => {
				new TestClass('foo');
			}).to.throw(Error);
		});
	});
});
