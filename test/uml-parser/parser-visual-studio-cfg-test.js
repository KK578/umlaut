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
	});

	it('should handle conditions with a list with 2 items for linked preconditions at the start', function () {
		const result = testee('({0,1} a == b)');

		expect(result).to.be.instanceOf(Array).and.have.length(1);
		expect(result[0].comparison).to.equal('Equal');
		expect(result[0].arguments).to.include('a', 'b');
		expect(result[0].linkedPreconditions).to.be.instanceOf(Array).and.have.length(2);
	});

	it('should handle conditions with a list with 3 items for linked preconditions at the start', function () {
		const result = testee('({0,1,2} a == b)');

		expect(result).to.be.instanceOf(Array).and.have.length(1);
		expect(result[0].comparison).to.equal('Equal');
		expect(result[0].arguments).to.include('a', 'b');
		expect(result[0].linkedPreconditions).to.be.instanceOf(Array).and.have.length(3);
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
	});
});
