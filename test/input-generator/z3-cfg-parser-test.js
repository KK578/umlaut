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
		expect(result).to.contain.key('values');

		expect(result.id).to.be.a('string').and.equal('Valid');
		expect(result.values).to.have.key('a');
		expect(result.values.a).to.be.a('number').and.equal(0);
	});

	it('should handle generic string with spaces written just before the list in [[]]', () => {
		const result = testee('[[This is a string]] sat ((a 0))');

		expect(result).to.contain.key('id');
		expect(result).to.contain.key('values');

		expect(result.id).to.be.a('string').and.equal('This is a string');
		expect(result.values).to.have.key('a');
		expect(result.values.a).to.be.a('number').and.equal(0);
	});

	it('should handle a UUID written just before the list in [[]]', () => {
		const result = testee('[[12345678-abcd-efab-cdef-123456789012]] sat ((a 0))');

		expect(result).to.contain.keys(['id', 'values']);

		expect(result.id).to.be.a('string').and.equal('12345678-abcd-efab-cdef-123456789012');
		expect(result.values).to.have.key('a');
		expect(result.values.a).to.be.a('number').and.equal(0);
	});

	it('should handle a UUID written before the list in [[]] after a line break', () => {
		const result = testee(`[[12345678-abcd-efab-cdef-123456789012]]
			sat
			((a 0))`);

		expect(result).to.contain.keys(['id', 'values']);

		expect(result.id).to.be.a('string').and.equal('12345678-abcd-efab-cdef-123456789012');
		expect(result.values).to.have.key('a');
		expect(result.values.a).to.be.a('number').and.equal(0);
	});

	it('should correctly handle an unsatisfiable set of assertions', () => {
		const result = testee('[[12345678-abcd-efab-cdef-123456789012]] unsat (error "line 1 column 1: model is not available")');

		expect(result).to.contain.keys(['id', 'values']);

		expect(result.id).to.be.a('string').and.equal('12345678-abcd-efab-cdef-123456789012');
		expect(result.unsatisfiable).to.be.ok;
		expect(result.values).to.not.exist;
	});

	it('should handle multiple objects consecutively', () => {
		const result = testee(`[[First]] sat ((a 0)(b (- 1)))
			[[Second]] sat ((a 0)(b 38))`);

		expect(result).to.be.instanceOf(Array);

		expect(result[0]).to.contain.keys(['id', 'values']);
		expect(result[0].id).to.equal('First');
		expect(result[0].values).to.contain.keys(['a', 'b']);
		expect(result[0].values.a).to.be.a('number').and.equal(0);
		expect(result[0].values.b).to.be.a('number').and.equal(-1);

		expect(result[1]).to.contain.keys(['id', 'values']);
		expect(result[1].id).to.equal('Second');
		expect(result[1].values).to.contain.keys(['a', 'b']);
		expect(result[1].values.a).to.be.a('number').and.equal(0);
		expect(result[1].values.b).to.be.a('number').and.equal(38);
	});

	it('should handle multiple objects consecutively including unsatisfiable', () => {
		const result = testee(`[[First]] sat ((a 0)(b (- 1)))
			[[Second]] unsat (error "line 5 column 5: model is not available")
			[[Third]] sat ((a 0)(b 38))`);

		expect(result).to.be.instanceOf(Array);

		expect(result[0]).to.contain.keys(['id', 'values']);
		expect(result[0].id).to.equal('First');
		expect(result[0].values).to.contain.keys(['a', 'b']);
		expect(result[0].values.a).to.be.a('number').and.equal(0);
		expect(result[0].values.b).to.be.a('number').and.equal(-1);

		expect(result[1].id).to.be.a('string').and.equal('12345678-abcd-efab-cdef-123456789012');
		expect(result[1].unsatisfiable).to.be.ok;
		expect(result[1].values).to.not.exist;

		expect(result[2]).to.contain.keys(['id', 'values']);
		expect(result[2].id).to.equal('Second');
		expect(result[2].values).to.contain.keys(['a', 'b']);
		expect(result[2].values.a).to.be.a('number').and.equal(0);
		expect(result[2].values.b).to.be.a('number').and.equal(38);
	});
});
