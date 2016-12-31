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
		const result = testee('((a 0) (b 1))');

		expect(result).to.contain.key('a');
		expect(result).to.contain.key('b');

		expect(result.a).to.be.a('number').and.equal(0);
		expect(result.b).to.be.a('number').and.equal(1);
	});
});
