const testee = require('../../../input-generator/smt-solver/z3-runner/value-cfg-parser.js');

describe('CFG Parser for z3 Values', function () {
	it('should handle a single key value pair', function () {
		const result = testee('(a 0)');

		expect(result).to.have.key('a');
		expect(result.a).to.be.a('number').and.equal(0);
	});

	it('should handle list with a single key value pair', function () {
		const result = testee('((a 0))');

		expect(result).to.have.key('a');
		expect(result.a).to.be.a('number').and.equal(0);
	});

	it('should handle list with multiple key value pairs', function () {
		const result = testee('((a 0)(b 1))');

		expect(result).to.contain.keys(['a', 'b']);

		expect(result.a).to.be.a('number').and.equal(0);
		expect(result.b).to.be.a('number').and.equal(1);
	});

	it('should handle list with multiple key value pairs with line breaks', function () {
		const result = testee(`((a 0)
			(b 1)
			(c 4))`);

		expect(result).to.contain.keys(['a', 'b', 'c']);

		expect(result.a).to.be.a('number').and.equal(0);
		expect(result.b).to.be.a('number').and.equal(1);
		expect(result.c).to.be.a('number').and.equal(4);
	});

	it('should handle Valid keyword written just before the list in [[]]', function () {
		const result = testee('[[Valid]] sat ((a 0))');

		expect(result).to.contain.key('id');
		expect(result).to.contain.key('arguments');

		expect(result.id).to.be.a('string').and.equal('Valid');
		expect(result.arguments).to.have.key('a');
		expect(result.arguments.a).to.be.a('number').and.equal(0);
	});

	it('should handle a UUID written just before the list in [[]]', function () {
		const result = testee('[[12345678-abcd-efab-cdef-123456789012]] sat ((a 0))');

		expect(result).to.contain.keys(['id', 'arguments']);

		expect(result.id).to.be.a('string').and.equal('12345678-abcd-efab-cdef-123456789012');
		expect(result.arguments).to.have.key('a');
		expect(result.arguments.a).to.be.a('number').and.equal(0);
	});

	it('should handle a UUID written before the list in [[]] after a line break', function () {
		const result = testee(`[[12345678-abcd-efab-cdef-123456789012]]
			sat
			((a 0))`);

		expect(result).to.contain.keys(['id', 'arguments']);

		expect(result.id).to.be.a('string').and.equal('12345678-abcd-efab-cdef-123456789012');
		expect(result.arguments).to.have.key('a');
		expect(result.arguments.a).to.be.a('number').and.equal(0);
	});

	it('should correctly handle an unsatisfiable set of assertions', function () {
		const result = testee('[[12345678-abcd-efab-cdef-123456789012]] unsat (error "line 1 column 1: model is not available")');

		expect(result).to.contain.keys(['id', 'unsatisfiable']);

		expect(result.id).to.be.a('string').and.equal('12345678-abcd-efab-cdef-123456789012');
		expect(result.unsatisfiable).to.be.ok;
		expect(result.arguments).to.not.exist;
	});

	const uuidList = [
		'12345678-abcd-efab-cdef-123456789012',
		'87654321-abcd-efab-cdef-987654321000',
		'aaaaaaaa-bbbb-cccc-dddd-eeeeffffffff',
		'abcdefab-cdef-abcd-efab-cdefabcdefab'
	];

	uuidList.forEach((_, i, list) => {
		it(`should handle ${i + 1} UUID strings within [[..]]]`, function () {
			// Take the first (i + 1) uuids from the list and join with commas.
			const uuidString = list.slice(0, i + 1).join(',');
			const result = testee(`[[${uuidString}]] sat ((a 0))`);

			expect(result).to.contain.keys(['id', 'arguments']);

			expect(result.id).to.be.a('string').and.equal(uuidString);
			expect(result.arguments).to.have.key('a');
			expect(result.arguments.a).to.be.a('number').and.equal(0);
		});
	});

	it('should handle multiple objects consecutively', function () {
		const result = testee(`[[12345678-abcd-efab-cdef-123456789012]] sat ((a 0)(b (- 1)))
			~~[[87654321-abcd-efab-cdef-987654321000]] sat ((a 0)(b 38))`);

		expect(result).to.be.instanceOf(Array);

		expect(result[0]).to.contain.keys(['id', 'arguments']);
		expect(result[0].id).to.equal('12345678-abcd-efab-cdef-123456789012');
		expect(result[0].arguments).to.contain.keys(['a', 'b']);
		expect(result[0].arguments.a).to.be.a('number').and.equal(0);
		expect(result[0].arguments.b).to.be.a('number').and.equal(-1);

		expect(result[1]).to.contain.keys(['id', 'arguments']);
		expect(result[1].id).to.equal('87654321-abcd-efab-cdef-987654321000');
		expect(result[1].arguments).to.contain.keys(['a', 'b']);
		expect(result[1].arguments.a).to.be.a('number').and.equal(0);
		expect(result[1].arguments.b).to.be.a('number').and.equal(38);
	});

	it('should handle multiple objects consecutively including unsatisfiable', function () {
		const result = testee(`[[Valid]] sat ((a 0)(b (- 1)))
			~~[[12345678-abcd-efab-cdef-123456789012]] unsat (error "line 5 column 5: model is not available")
			~~[[87654321-abcd-efab-cdef-987654321000]] sat ((a 0)(b 38))`);

		expect(result).to.be.instanceOf(Array);

		expect(result[0]).to.contain.keys(['id', 'arguments']);
		expect(result[0].id).to.equal('Valid');
		expect(result[0].arguments).to.contain.keys(['a', 'b']);
		expect(result[0].arguments.a).to.be.a('number').and.equal(0);
		expect(result[0].arguments.b).to.be.a('number').and.equal(-1);

		expect(result[1].id).to.be.a('string').and.equal('12345678-abcd-efab-cdef-123456789012');
		expect(result[1].unsatisfiable).to.be.ok;
		expect(result[1].arguments).to.not.exist;

		expect(result[2]).to.contain.keys(['id', 'arguments']);
		expect(result[2].id).to.equal('87654321-abcd-efab-cdef-987654321000');
		expect(result[2].arguments).to.contain.keys(['a', 'b']);
		expect(result[2].arguments.a).to.be.a('number').and.equal(0);
		expect(result[2].arguments.b).to.be.a('number').and.equal(38);
	});

	describe('Numbers', function () {
		describe('Integer', function () {
			it('should handle simple integer values', function () {
				const result = testee('(a 5)');

				expect(result).to.have.key('a');
				expect(result.a).to.be.a('number').and.equal(5);
			});

			it('should handle larger integer values', function () {
				const result = testee('(a 12345)');

				expect(result).to.have.key('a');
				expect(result.a).to.be.a('number').and.equal(12345);
			});

			it('should handle simple negative integer values', function () {
				const result = testee('(a (- 1))');

				expect(result).to.have.key('a');
				expect(result.a).to.be.a('number').and.equal(-1);
			});

			it('should handle larger negative integer values', function () {
				const result = testee('(a (- 12345))');

				expect(result).to.have.key('a');
				expect(result.a).to.be.a('number').and.equal(-12345);
			});
		});

		describe('Float/Double', function () {
			it('should handle 0', function () {
				const result = testee('(a 0.0)');

				expect(result).to.have.key('a');
				expect(result.a).to.be.a('number').and.equal(0);
			});

			it('should handle simple decimal values', function () {
				const result = testee('(a 1.1)');

				expect(result).to.have.key('a');
				expect(result.a).to.be.a('number').and.equal(1.1);
			});

			it('should handle larger decimal values', function () {
				const result = testee('(a 1234.5678)');

				expect(result).to.have.key('a');
				expect(result.a).to.be.a('number').and.equal(1234.5678);
			});

			it('should handle simple negative decimal values', function () {
				const result = testee('(a (- 1.2))');

				expect(result).to.have.key('a');
				expect(result.a).to.be.a('number').and.equal(-1.2);
			});

			it('should handle larger negative decimal values', function () {
				const result = testee('(a (- 1234.5678))');

				expect(result).to.have.key('a');
				expect(result.a).to.be.a('number').and.equal(-1234.5678);
			});
		});
	});

	describe('Booleans', function () {
		it('should handle true', function () {
			const result = testee('(a true)');

			expect(result).to.have.key('a');
			expect(result.a).to.be.a('boolean').and.be.true;
		});

		it('should handle false', function () {
			const result = testee('(a false)');

			expect(result).to.have.key('a');
			expect(result.a).to.be.a('boolean').and.not.be.true;
		});
	});
});
