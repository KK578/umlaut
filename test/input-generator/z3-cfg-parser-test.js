const chai = require('chai');
const expect = chai.expect;

const testee = require('../../input-generator/smt-solver/z3-runner/value-cfg-parser.js');

describe('CFG Parser for z3 Values', () => {
	it('should handle a single key value pair', () => {
		const result = testee('(a 0)');

		expect(result).to.have.key('a');
		expect(result.a).to.be.a('number').and.equal(0);
	});

	it('should handle negative integer values', () => {
		const result = testee('((a (- 1)))');

		expect(result).to.have.key('a');
		expect(result.a).to.be.a('number').and.equal(-1);
	});

	it('should handle list with a single key value pair', () => {
		const result = testee('((a 0))');

		expect(result).to.have.key('a');
		expect(result.a).to.be.a('number').and.equal(0);
	});

	it('should handle list with multiple key value pairs', () => {
		const result = testee('((a 0)(b 1))');

		expect(result).to.contain.keys(['a', 'b']);

		expect(result.a).to.be.a('number').and.equal(0);
		expect(result.b).to.be.a('number').and.equal(1);
	});

	it('should handle list with multiple key value pairs with line breaks', () => {
		const result = testee(`((a 0)
			(b 1)
			(c 4))`);

		expect(result).to.contain.keys(['a', 'b', 'c']);

		expect(result.a).to.be.a('number').and.equal(0);
		expect(result.b).to.be.a('number').and.equal(1);
		expect(result.c).to.be.a('number').and.equal(4);
	});

	it('should handle Valid keyword written just before the list in [[]]', () => {
		const result = testee('[[Valid]] sat ((a 0))');

		expect(result).to.contain.key('id');
		expect(result).to.contain.key('arguments');

		expect(result.id).to.be.a('string').and.equal('Valid');
		expect(result.arguments).to.have.key('a');
		expect(result.arguments.a).to.be.a('number').and.equal(0);
	});

	it('should handle a UUID written just before the list in [[]]', () => {
		const result = testee('[[12345678-abcd-efab-cdef-123456789012]] sat ((a 0))');

		expect(result).to.contain.keys(['id', 'arguments']);

		expect(result.id).to.be.a('string').and.equal('12345678-abcd-efab-cdef-123456789012');
		expect(result.arguments).to.have.key('a');
		expect(result.arguments.a).to.be.a('number').and.equal(0);
	});

	it('should handle a UUID written before the list in [[]] after a line break', () => {
		const result = testee(`[[12345678-abcd-efab-cdef-123456789012]]
			sat
			((a 0))`);

		expect(result).to.contain.keys(['id', 'arguments']);

		expect(result.id).to.be.a('string').and.equal('12345678-abcd-efab-cdef-123456789012');
		expect(result.arguments).to.have.key('a');
		expect(result.arguments.a).to.be.a('number').and.equal(0);
	});

	it('should correctly handle an unsatisfiable set of assertions', () => {
		const result = testee('[[12345678-abcd-efab-cdef-123456789012]] unsat (error "line 1 column 1: model is not available")');

		expect(result).to.contain.keys(['id', 'unsatisfiable']);

		expect(result.id).to.be.a('string').and.equal('12345678-abcd-efab-cdef-123456789012');
		expect(result.unsatisfiable).to.be.ok;
		expect(result.arguments).to.not.exist;
	});

	it('should handle multiple objects consecutively', () => {
		const result = testee(`[[12345678-abcd-efab-cdef-123456789012]] sat ((a 0)(b (- 1)))
			\\[[87654321-abcd-efab-cdef-987654321000]] sat ((a 0)(b 38))`);

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

	it('should handle multiple objects consecutively including unsatisfiable', () => {
		const result = testee(`[[Valid]] sat ((a 0)(b (- 1)))
			\\[[12345678-abcd-efab-cdef-123456789012]] unsat (error "line 5 column 5: model is not available")
			\\[[87654321-abcd-efab-cdef-987654321000]] sat ((a 0)(b 38))`);

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
});
