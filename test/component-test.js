const path = require('path');

const chai = require('chai');
const chaiAsPromised = require('chai-as-promised');
const chaiFiles = require('chai-files');

chai.use(chaiAsPromised);
chai.use(chaiFiles);

const expect = chai.expect;
const file = chaiFiles.file;
const yeomanHelpers = require('yeoman-test');

const promises = require('../util/promises.js');

describe('Component Tests', () => {
	describe('Uml-Parser', () => {
		describe('Visual Studio Parser', () => {
			let testee;

			before(() => {
				testee = require('../uml-parser/parsers/visual-studio/index.js');
			});

			it('should fail to parse a non XML string');
			it('should fail to parse an arbitrary XML string');
			it('should parse if the XML root contains a "modelStoreModel" attribute');
			it('should parse if the XML root contains a "logicalClassDesignerModel" attribute');
			it('should parse Visual Studio model with class with no variables');
			it('should parse Visual Studio model with class with no methods');
			it('should parse Visual Studio model with no classes');
			it('should parse Visual Studio model with multiple classes');

			describe('SimpleMath Test Fixture', () => {
				it('should successfully be detected as parsable', () => {
					const fixture = path.join(__dirname, './fixtures/SimpleMath/ModelDefinition/SimpleMath.uml');

					return promises.fsReadFile(fixture).then((data) => {
						const promise = testee.detect(data);

						return expect(promise).to.be.fulfilled;
					}).then((result) => {
						expect(result).to.be.ok;
					});
				});

				it('should successfully be parsed', () => {
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
	});

	describe('Input-Ienerator', () => {
		let testee;

		describe('SMT-Solver', () => {
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

	describe('Test-Generator', () => {
		describe('JUnit', () => {
			beforeEach(() => {
				return yeomanHelpers.run(path.join(__dirname, '../generators/junit'))
					.inDir('test/tmp/junit/')
					.withArguments([
						// Relative to the above directory.
						'../../fixtures/test-generator/uml/',
						'../../fixtures/test-generator/smt/'
					]);
			});

			it('should make a test suite for SimpleMath', () => {
				expect(file('build/SimpleMathTest.java')).to.exist;
			});

			afterEach(() => {
				// Reset location due to changing from helpers running in specific directory.
				process.chdir('../../../');
			});
		});

		describe('NUnit', () => {
			beforeEach(() => {
				return yeomanHelpers.run(path.join(__dirname, '../generators/nunit'))
					.inDir('test/tmp/nunit/')
					.withArguments([
						// Relative to the above directory.
						'../../fixtures/test-generator/uml/',
						'../../fixtures/test-generator/smt/'
					]);
			});

			it('should make a test suite for SimpleMath', () => {
				expect(file('build/SimpleMathTest.cs')).to.exist;
			});

			afterEach(() => {
				// Reset location due to changing from helpers running in specific directory.
				process.chdir('../../../');
			});
		});
	});
});
