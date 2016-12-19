const chai = require('chai');
const chaiAsPromised = require('chai-as-promised');
const path = require('path');

chai.use(chaiAsPromised);

const expect = chai.expect;

const testee = require('../../src/input-generator/smt-solver/index.js');

describe('Input Generator SMT Solver', () => {
	it('should run against SimpleMath test fixture', () => {
		const fixture = require(path.join(__dirname, '../fixtures/test-generator/uml/SimpleMath.json'));
		const promise = testee(fixture);

		return expect(promise).to.be.fulfilled;
	});
});
