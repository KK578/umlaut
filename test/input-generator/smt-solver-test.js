const chai = require('chai');
const chaiAsPromised = require('chai-as-promised');
const path = require('path');

chai.use(chaiAsPromised);

const expect = chai.expect;

const testee = require('../../input-generator/smt-solver/index.js');

describe('Input Generator SMT Solver', () => {
	before((done) => {
		// HACK: Create folder here temporarily.
		const fs = require('fs');

		fs.mkdir('build', () => {
			fs.mkdir('build/smt/', () => {
				fs.mkdir('build/smt/SimpleMath/', () => {
					done();
				});
			});
		});
	});

	it('should run against SimpleMath test fixture', () => {
		const fixture = require(path.join(__dirname, '../fixtures/test-generator/uml/SimpleMath.json'));
		const promise = testee(fixture);

		return expect(promise).to.be.fulfilled;
	});
});