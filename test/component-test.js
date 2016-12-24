const chai = require('chai');
const chaiAsPromised = require('chai-as-promised');
const path = require('path');

chai.use(chaiAsPromised);

const expect = chai.expect;

const promises = require('../util/promises.js');

describe('Component Tests', () => {
	describe('uml-parser', () => {
		describe('Visual Studio', () => {
			let testee;

			before(() => {
				testee = require('../uml-parser/parsers/visual-studio/index.js');
			});

			it('should state it can parse Visual Studio SimpleMath test fixture', () => {
				const fixture = path.join(__dirname, './fixtures/SimpleMath/ModelDefinition/SimpleMath.uml');

				return promises.fsReadFile(fixture).then((data) => {
					const promise = testee.detect(data);

					return expect(promise).to.be.fulfilled;
				}).then((result) => {
					expect(result).to.be.ok;
				});
			});

			it('should parse Visual Studio SimpleMath test fixture', () => {
				const fixture = path.join(__dirname, './fixtures/SimpleMath/ModelDefinition/SimpleMath.uml');

				return promises.fsReadFile(fixture).then((data) => {
					const promise = testee.parse(data);

					return expect(promise).to.be.fulfilled;
				}).then((result) => {
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

	describe('test-generator', () => {});
});
