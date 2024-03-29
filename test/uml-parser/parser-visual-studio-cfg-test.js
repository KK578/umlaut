const comparisons = require('../../util/comparisons.json');
const testee = require('../../uml-parser/parsers/visual-studio/condition-cfg-parser.js');

describe('CFG Parser for Visual Studio Condition Strings', function () {
	it('should handle a single condition', function () {
		const result = testee('(a == b)');

		expect(result).to.be.instanceOf(Array).and.have.length(1);
		expect(result[0].comparison).to.equal('Equal');
		expect(result[0].arguments).to.include('a', 'b');
		expect(result[0].exception).to.be.undefined;
	});

	it('should handle a single condition with a not flag', function () {
		const result = testee('(a not == b)');

		expect(result).to.be.instanceOf(Array).and.have.length(1);
		expect(result[0].comparison).to.equal('Equal');
		expect(result[0].arguments).to.include('a', 'b');
		expect(result[0].inverted).to.be.true;
		expect(result[0].exception).to.be.undefined;
	});

	it('should not handle a condition with a not flag if the comparison is not invertable', function () {
		expect(() => {
			testee('(a not >= b)');
		}).to.throw(Error);
	});

	it('should handle a single condition with an exception', function () {
		const result = testee('(a == b Exception:FooException)');

		expect(result).to.be.instanceOf(Array).and.have.length(1);
		expect(result[0].comparison).to.equal('Equal');
		expect(result[0].arguments).to.include('a', 'b');
		expect(result[0].exception).to.equal('FooException');
	});

	it('should handle conditions with a list with 1 item for linked preconditions at the start', function () {
		const result = testee('({0} a == b)');

		expect(result).to.be.instanceOf(Array).and.have.length(1);
		expect(result[0].comparison).to.equal('Equal');
		expect(result[0].arguments).to.include('a', 'b');
		expect(result[0].linkedPreconditions).to.be.instanceOf(Array).and.have.length(1);
		expect(result[0].linkedPreconditions[0]).to.be.a('number');
	});

	it('should handle conditions with a list with 2 items for linked preconditions at the start', function () {
		const result = testee('({0;1} a == b)');

		expect(result).to.be.instanceOf(Array).and.have.length(1);
		expect(result[0].comparison).to.equal('Equal');
		expect(result[0].arguments).to.include('a', 'b');
		expect(result[0].linkedPreconditions).to.be.instanceOf(Array).and.have.length(2);
		expect(result[0].linkedPreconditions[0]).to.be.a('number');
		expect(result[0].linkedPreconditions[1]).to.be.a('number');
	});

	it('should handle conditions with a list with 3 items for linked preconditions at the start', function () {
		const result = testee('({0;1;2} a == b)');

		expect(result).to.be.instanceOf(Array).and.have.length(1);
		expect(result[0].comparison).to.equal('Equal');
		expect(result[0].arguments).to.include('a', 'b');
		expect(result[0].linkedPreconditions).to.be.instanceOf(Array).and.have.length(3);
		expect(result[0].linkedPreconditions[0]).to.be.a('number');
		expect(result[0].linkedPreconditions[1]).to.be.a('number');
		expect(result[0].linkedPreconditions[2]).to.be.a('number');
	});

	it('should handle multiple conditions split by ","', function () {
		const result = testee('(a == b),(b > c)');

		expect(result).to.be.instanceOf(Array).and.have.length(2);

		expect(result[0].comparison).to.equal('Equal');
		expect(result[0].arguments).to.include('a', 'b');
		expect(result[1].comparison).to.equal('GreaterThan');
		expect(result[1].arguments).to.include('b', 'c');
	});

	describe('Comparisons', function () {
		comparisons.forEach((comparison) => {
			it(`should handle comparison "${comparison.name}"`, function () {
				const result = testee(`(a ${comparison.symbol} b)`);

				expect(result).to.be.instanceOf(Array).and.have.length(1);
				expect(result[0].comparison).to.equal(comparison.name);
				expect(result[0].arguments).to.include('a', 'b');
			});
		});

		it('should not allow a comparison named "VeryFake"', function () {
			expect(testee.bind(testee, '(a VeryFake b)')).to.throw(Error);
		});
	});

	describe('Numeric', function () {
		it('should parse integer values to numbers', function () {
			const result = testee('(a > 0)');

			expect(result).to.be.instanceOf(Array).and.have.length(1);
			expect(result[0].comparison).to.equal('GreaterThan');
			expect(result[0].arguments).to.include('a', 0);
			expect(result[0].arguments).to.not.include('0');
		});

		it('should parse float values to numbers', function () {
			const result = testee('(a > 1.5)');

			expect(result).to.be.instanceOf(Array).and.have.length(1);
			expect(result[0].comparison).to.equal('GreaterThan');
			expect(result[0].arguments).to.include('a', 1.5);
			expect(result[0].arguments).to.not.include('1.0');
		});
	});

	describe('Boolean', function () {
		it('should parse true', function () {
			const result = testee('(a == true)');

			expect(result).to.be.instanceOf(Array).and.have.length(1);
			expect(result[0].comparison).to.equal('Equal');
			expect(result[0].arguments).to.include('a', true);
			expect(result[0].arguments).to.not.include('true');
		});

		it('should parse false', function () {
			const result = testee('(a == false)');

			expect(result).to.be.instanceOf(Array).and.have.length(1);
			expect(result[0].comparison).to.equal('Equal');
			expect(result[0].arguments).to.include('a', false);
			expect(result[0].arguments).to.not.include('false');
		});
	});

	describe('Functions', function () {
		it('should parse function calls with no parameters', function () {
			const result = testee('(foo():Integer > 0)');

			expect(result).to.be.instanceOf(Array).and.have.length(1);
			expect(result[0].comparison).to.equal('GreaterThan');
			expect(result[0].arguments[0]).to.be.an('object');
			expect(result[0].arguments[1]).to.equal(0);
			expect(result[0].arguments).to.not.include('foo()');

			const functionCall = result[0].arguments[0];

			expect(functionCall.label).to.equal('FunctionCall');
			expect(functionCall.type).to.equal('Integer');
			expect(functionCall.name).to.equal('foo');
			expect(functionCall.arguments).to.be.an('object').and.be.empty;
		});

		it('should parse function calls with 1 parameter', function () {
			const result = testee('(foo(5:Integer):Integer > 0)');

			expect(result).to.be.instanceOf(Array).and.have.length(1);
			expect(result[0].comparison).to.equal('GreaterThan');
			expect(result[0].arguments[0]).to.be.an('object');
			expect(result[0].arguments[1]).to.equal(0);
			expect(result[0].arguments).to.not.include('foo()');

			const functionCall = result[0].arguments[0];

			expect(functionCall.label).to.equal('FunctionCall');
			expect(functionCall.type).to.equal('Integer');
			expect(functionCall.name).to.equal('foo');
			expect(functionCall.arguments).to.be.instanceOf(Array).and.have.length(1);
			expect(functionCall.arguments[0]).to.deep.equal({ type: 'Integer', value: 5 });
		});

		it('should parse function calls with 2 parameter', function () {
			const result = testee('(foo(5:Integer, 7:Integer):Integer > 0)');

			expect(result).to.be.instanceOf(Array).and.have.length(1);
			expect(result[0].comparison).to.equal('GreaterThan');
			expect(result[0].arguments[0]).to.be.an('object');
			expect(result[0].arguments[1]).to.equal(0);
			expect(result[0].arguments).to.not.include('foo()');

			const functionCall = result[0].arguments[0];

			expect(functionCall.label).to.equal('FunctionCall');
			expect(functionCall.type).to.equal('Integer');
			expect(functionCall.name).to.equal('foo');
			expect(functionCall.arguments).to.be.instanceOf(Array).and.have.length(2);
			expect(functionCall.arguments[0]).to.deep.equal({ type: 'Integer', value: 5 });
			expect(functionCall.arguments[1]).to.deep.equal({ type: 'Integer', value: 7 });
		});

		it('should parse function calls with no paramaters different spacing styles', function () {
			const strings = [
				'(foo ():Integer > 0)',
				'(foo ( ):Integer > 0)'
			];

			strings.forEach((s) => {
				const result = testee(s);

				expect(result).to.be.instanceOf(Array).and.have.length(1);
				expect(result[0].comparison).to.equal('GreaterThan');
				expect(result[0].arguments[0]).to.be.an('object');
				expect(result[0].arguments[1]).to.equal(0);
				expect(result[0].arguments).to.not.include('foo()');

				const functionCall = result[0].arguments[0];

				expect(functionCall.label).to.equal('FunctionCall');
				expect(functionCall.type).to.equal('Integer');
				expect(functionCall.name).to.equal('foo');
				expect(functionCall.arguments).to.be.an('object').and.be.empty;
			});
		});
	});
});
