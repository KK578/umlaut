const path = require('path');

const chai = require('chai');
const chaiAsPromised = require('chai-as-promised');
const chaiFiles = require('chai-files');
const yeomanHelpers = require('yeoman-test');
const expect = chai.expect;
const file = chaiFiles.file;

chai.use(chaiAsPromised);
chai.use(chaiFiles);

describe('NUnit', () => {
	beforeEach(() => {
		const fixture = require(path.join(__dirname, '../fixtures/inputs/SimpleMath.json'));

		return yeomanHelpers.run(path.join(__dirname, '../../generators/app'))
			.inDir('test/tmp/nunit/')
			.withOptions({
				model: JSON.stringify(fixture),
				framework: 'nunit'
			});
	});

	it('should make a test suite for SimpleMath', () => {
		expect(file('build/SimpleMathTest.cs')).to.exist;
	});

	afterEach(() => {
		// Reset location due to changing from helpers running in specific directory.
		process.chdir('../../../');
	});
});
