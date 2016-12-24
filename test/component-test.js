const chai = require('chai');
const chaiAsPromised = require('chai-as-promised');
const path = require('path');

chai.use(chaiAsPromised);

const expect = chai.expect;

describe('Component Tests', () => {
	describe('uml-parser', () => {
		describe('Visual Studio', () => {
			let testee;

			before(() => {
				testee = require('../uml-parser/index.js');
			});

			it('should parse Visual Studio SimpleMath test fixture', () => {
				const fixture = path.join(__dirname, './fixtures/SimpleMath/ModelDefinition/SimpleMath.uml');
				const promise = testee(fixture);

				return expect(promise).to.be.fulfilled.then((result) => {
					expect(result.SimpleMath).to.be.an('object');
				});
			});
		});
	});

	describe('input-generator', () => {
		let testee;
		describe('smt-solver', () => {
			before(() => {
				testee = require('../input-generator/smt-solver/index.js');
			});

			it('should run against SimpleMath test fixture', () => {
				const fixture = require(path.join(__dirname, './fixtures/test-generator/uml/SimpleMath.json'));
				const promise = testee(fixture);

				return expect(promise).to.be.fulfilled.then((result) => {
					expect(result.SimpleMath).to.be.an('object');
				});
			});
		});
	});

	describe('test-generator', () => {})
});
