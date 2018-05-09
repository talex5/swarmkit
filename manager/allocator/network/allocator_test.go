package network

import (
	. "github.com/onsi/ginkgo"
	. "github.com/onsi/gomega"

	"github.com/docker/swarmkit/api"
	"github.com/docker/swarmkit/manager/allocator/network/errors"

	// gomock code. usually, i would not use gomock, i would write a fake.
	// but because this component is almost entirely a shim between the caller
	// and the lower level interfaces, mocking them out will save a lot of
	// time and effort over building rather complex fakes.
	driver "github.com/docker/swarmkit/mocks/mock_driver"
	ipam "github.com/docker/swarmkit/mocks/mock_ipam"
	port "github.com/docker/swarmkit/mocks/mock_port"
	"github.com/golang/mock/gomock"
)

// the creation of port.Proposal objects is restricted to the port package, so
// we'll create a quick fake here. using a fake instead of a proper generated
// gomock mock because gomock is too heavyweight for this lightweight
// dependency.
type fakeProposal struct {
	ports       []*api.PortConfig
	isNoop      bool
	isCommitted bool
}

func (f *fakeProposal) Ports() []*api.PortConfig {
	return f.ports
}

func (f *fakeProposal) IsNoop() bool {
	return f.isNoop
}

func (f *fakeProposal) Commit() {
	f.isCommitted = true
}

var _ = Describe("network.Allocator", func() {
	var (
		a *allocator

		// initial state, which will be passed to Restore befor each spec
		initNetworks []*api.Network
		initServices []*api.Service
		initTasks    []*api.Task
		initNodes    []*api.Node

		// mock sub-allocators
		mockCtrl   *gomock.Controller
		mockIpam   *ipam.MockAllocator
		mockDriver *driver.MockAllocator
		mockPort   *port.MockAllocator
	)

	BeforeEach(func() {
		// nil out the initialization lists so that they're fresh for every
		// test
		initNetworks = nil
		initServices = nil
		initTasks = nil
		initNodes = nil
		// set up the mocks, and create an Allocator that uses them
		mockCtrl = gomock.NewController(GinkgoT())
		mockIpam = ipam.NewMockAllocator(mockCtrl)
		mockDriver = driver.NewMockAllocator(mockCtrl)
		mockPort = port.NewMockAllocator(mockCtrl)

		a = newAllocatorWithComponents(mockIpam, mockDriver, mockPort)
	})

	AfterEach(func() {
		// don't forget to finish the mock
		mockCtrl.Finish()
	})

	Describe("Restoring", func() {
		var (
			err error
		)
		JustBeforeEach(func() {
			err = a.Restore(initNetworks, initServices, initTasks, initNodes)
		})

		Context("when there is no state to restore", func() {
			BeforeEach(func() {
				mockPort.EXPECT().Restore([]*api.Endpoint{})
				mockIpam.EXPECT().Restore(nil, []*api.Endpoint{}, []*api.NetworkAttachment{}).Return(nil)
				mockDriver.EXPECT().Restore(nil).Return(nil)
			})
			It("should return no error", func() {
				Expect(err).ToNot(HaveOccurred())
			})
		})
		Context("when there are some networks allocated", func() {
			BeforeEach(func() {
				initNetworks = []*api.Network{
					{
						ID: "fooNet",
					},
					{
						ID: "localnet",
					},
				}
				// fooNet will be global, but localnet will be local
				mockDriver.EXPECT().IsNetworkNodeLocal(initNetworks[0]).Return(false, nil)
				mockDriver.EXPECT().IsNetworkNodeLocal(initNetworks[1]).Return(true, nil)
				mockPort.EXPECT().Restore([]*api.Endpoint{})
				mockIpam.EXPECT().Restore(initNetworks, []*api.Endpoint{}, []*api.NetworkAttachment{}).Return(nil)
				mockDriver.EXPECT().Restore(initNetworks).Return(nil)
			})
			It("should return no error", func() {
				Expect(err).ToNot(HaveOccurred())
			})
			It("should restore ipam and driver state", func() {
				// empty case, because this will actually be handled by gomock,
				// which will fail if it doesn't call restore with the
				// networks. this spec has been left here for documentation
				// purposes
			})
			It("should keep track of node-local networks", func() {
				Expect(a.nodeLocalNetworks).To(HaveKey("localnet"))
				Expect(a.nodeLocalNetworks["localnet"]).To(Equal(initNetworks[1]))
			})
		})
		Context("when there are some services allocated", func() {
			BeforeEach(func() {
				// service that are initialized
				initServices = []*api.Service{
					// an empty service, should not be included in restore, but
					// should be included in our services tracking map
					{ID: "service0"},
					// a fully allocated service, should be included in the
					// restore, and should be tracked in the "allocated" map
					{
						ID:          "service1",
						SpecVersion: &api.Version{Index: 1},
						Endpoint: &api.Endpoint{
							Spec: &api.EndpointSpec{
								Mode: api.ResolutionModeVirtualIP,
							},
							VirtualIPs: []*api.Endpoint_VirtualIP{
								{NetworkID: "nw1", Addr: "192.168.1.1/24"},
								{NetworkID: "nw2", Addr: "192.168.2.1/24"},
							},
						},
						Spec: api.ServiceSpec{
							Endpoint: &api.EndpointSpec{
								Mode: api.ResolutionModeVirtualIP,
							},
							Task: api.TaskSpec{
								Networks: []*api.NetworkAttachmentConfig{
									{Target: "nw1"},
									{Target: "nw2"},
								},
							},
						},
					},
					// Partially allocated service, should be included in the
					// IPAM and Port restore, but should not
					{
						ID:          "service2",
						SpecVersion: &api.Version{Index: 2},
						Endpoint: &api.Endpoint{
							Spec: &api.EndpointSpec{
								Mode: api.ResolutionModeVirtualIP,
							},
							VirtualIPs: []*api.Endpoint_VirtualIP{
								{NetworkID: "nw1", Addr: "192.168.1.1/24"},
							},
						},
						Spec: api.ServiceSpec{
							Endpoint: &api.EndpointSpec{},
						},
					},
				}

				endpoints := []*api.Endpoint{initServices[1].Endpoint, initServices[2].Endpoint}
				mockPort.EXPECT().Restore(endpoints)
				mockIpam.EXPECT().Restore(nil, endpoints, []*api.NetworkAttachment{})
				mockDriver.EXPECT().Restore(nil)
			})

			It("should not return an error", func() {
				Expect(err).ToNot(HaveOccurred())
			})
			It("should restore ipam and port state of the service's endpoints", func() {
				// again, an empty spec, because this behavior is covered by
				// gomock doing its thing.
			})
			It("should mark service 0 & 1 as fully allocated, and not service 2", func() {
				Expect(a.services).To(And(
					HaveKey("service0"),
					HaveKey("service1"),
					Not(HaveKey("service2")),
				))
				Expect(a.services["service0"]).To(Equal(initServices[0]))
				Expect(a.services["service1"]).To(Equal(initServices[1]))
			})
		})
		Context("when some tasks are allocated", func() {
			BeforeEach(func() {
				initTasks = []*api.Task{
					// Empty task, should add any attachments
					{},
					{
						Networks: []*api.NetworkAttachment{
							{Network: &api.Network{ID: "foo"}, Addresses: []string{"192.168.1.4/24"}},
							{Network: &api.Network{ID: "bar"}, Addresses: []string{"192.168.2.4/24"}},
						},
					},
					{
						Networks: []*api.NetworkAttachment{
							{Network: &api.Network{ID: "baz"}, Addresses: []string{"192.168.3.4/24"}},
							{Network: &api.Network{ID: "bat"}, Addresses: []string{"192.168.4.4/24"}},
						},
					},
					{
						Networks: []*api.NetworkAttachment{
							{Network: &api.Network{ID: "local"}, Addresses: []string{"10.6.6.6"}},
						},
					},
				}

				// add the "local" network, which will be node-local
				local := &api.Network{
					ID: "local",
				}
				initNetworks = append(initNetworks, local)
				mockDriver.EXPECT().IsNetworkNodeLocal(local).Return(true, nil)

				attachments := append(initTasks[1].Copy().Networks, initTasks[2].Copy().Networks...)
				mockPort.EXPECT().Restore([]*api.Endpoint{})
				mockIpam.EXPECT().Restore(initNetworks, []*api.Endpoint{}, attachments).Return(nil)
				mockDriver.EXPECT().Restore(initNetworks).Return(nil)
			})
			It("should not return an error", func() {
				Expect(err).ToNot(HaveOccurred())
			})
			It("should restore the tasks", func() {
				// another empty spec, because gomock handles this
			})
		})
		Context("when some nodes are allocated", func() {
			BeforeEach(func() {
				initNodes = []*api.Node{
					{},
					{
						Attachments: []*api.NetworkAttachment{
							{Network: &api.Network{ID: "nw1"}, Addresses: []string{"192.168.1.4/24"}},
							{Network: &api.Network{ID: "nw2"}, Addresses: []string{"192.168.2.4/24"}},
						},
					},
					{
						Attachments: []*api.NetworkAttachment{
							{Network: &api.Network{ID: "nw3"}, Addresses: []string{"192.168.3.4/24"}},
							{Network: &api.Network{ID: "nw4"}, Addresses: []string{"192.168.4.4/24"}},
						},
					},
				}
				attachments := append(initNodes[1].Copy().Attachments, initNodes[2].Copy().Attachments...)
				mockPort.EXPECT().Restore([]*api.Endpoint{})
				mockIpam.EXPECT().Restore(nil, []*api.Endpoint{}, attachments).Return(nil)
				mockDriver.EXPECT().Restore(nil).Return(nil)
			})
			It("should not return an error", func() {
				Expect(err).ToNot(HaveOccurred())
			})
			It("should restore all of the attachments", func() {
				// empty case, handled by gomock
			})
		})
		Context("when some tasks and some nodes are allocated", func() {
			BeforeEach(func() {
				initNodes = []*api.Node{
					{},
					{
						Attachments: []*api.NetworkAttachment{
							{Network: &api.Network{ID: "nw1"}, Addresses: []string{"192.168.1.4/24"}},
							{Network: &api.Network{ID: "nw2"}, Addresses: []string{"192.168.2.4/24"}},
						},
					},
					{
						Attachments: []*api.NetworkAttachment{
							{Network: &api.Network{ID: "nw3"}, Addresses: []string{"192.168.3.4/24"}},
							{Network: &api.Network{ID: "nw4"}, Addresses: []string{"192.168.4.4/24"}},
						},
					},
				}
				initTasks = []*api.Task{
					// Empty task, should add any attachments
					{},
					{
						Networks: []*api.NetworkAttachment{
							{Network: &api.Network{}, Addresses: []string{"192.168.1.4/24"}},
							{Network: &api.Network{}, Addresses: []string{"192.168.2.4/24"}},
						},
					},
					{
						Networks: []*api.NetworkAttachment{
							{Network: &api.Network{}, Addresses: []string{"192.168.3.4/24"}},
							{Network: &api.Network{}, Addresses: []string{"192.168.4.4/24"}},
						},
					},
				}
				attachments := append(initTasks[1].Copy().Networks,
					append(initTasks[2].Copy().Networks,
						append(initNodes[1].Copy().Attachments,
							initNodes[2].Copy().Attachments...,
						)...,
					)...,
				)
				mockPort.EXPECT().Restore([]*api.Endpoint{})
				mockIpam.EXPECT().Restore(nil, []*api.Endpoint{}, attachments).Return(nil)
				mockDriver.EXPECT().Restore(nil).Return(nil)
			})
			It("should restore all of the attachments", func() {
				// handled by gomock
			})
			It("should return no error", func() {
				Expect(err).ToNot(HaveOccurred())
			})
		})
		Context("when errors occur", func() {
			BeforeEach(func() {
				// port can't return an error
				mockPort.EXPECT().Restore([]*api.Endpoint{})
			})
			Context("from the ipam allocator", func() {
				BeforeEach(func() {
					mockIpam.EXPECT().Restore(nil, []*api.Endpoint{}, []*api.NetworkAttachment{}).Return(errors.ErrBadState("foo"))
				})
				It("should return the error", func() {
					Expect(err).To(HaveOccurred())
					Expect(err).To(WithTransform(errors.IsErrBadState, BeTrue()))
				})
			})
			Context("from the driver allocator", func() {
				BeforeEach(func() {
					mockIpam.EXPECT().Restore(nil, []*api.Endpoint{}, []*api.NetworkAttachment{}).Return(nil)
					mockDriver.EXPECT().Restore(nil).Return(errors.ErrInternal("bar"))
				})
				It("should return the error", func() {
					Expect(err).To(HaveOccurred())
					Expect(err).To(WithTransform(errors.IsErrInternal, BeTrue()))
				})
			})
		})
	})
	// everything here gets its own describe block so that we can share the
	// common gomock setup
	Describe("Allocating and deallocating", func() {
		BeforeEach(func() {
			// Expectations for gomock to fulfill Restore. We pass an "Any"
			// matcher because we're not actually testing this behavior, we
			// just need to fill up the calls for gomock.
			mockPort.EXPECT().Restore(gomock.Any())
			mockIpam.EXPECT().Restore(gomock.Any(), gomock.Any(), gomock.Any()).Return(nil)
			mockDriver.EXPECT().Restore(gomock.Any()).Return(nil)
		})

		JustBeforeEach(func() {
			// just before, we should prepare for a bunch of calls to
			// IsNetworkNodeLocal
			for _, nw := range initNetworks {
				// use the driver name "local" to indicate node-local networks
				if nw.DriverState != nil && nw.DriverState.Name == "local" {
					mockDriver.EXPECT().IsNetworkNodeLocal(nw).Return(true, nil)
				} else {
					mockDriver.EXPECT().IsNetworkNodeLocal(nw).Return(false, nil)
				}
			}
			// Before we start, do a restore of all of these pre-populated
			// items.

			// NOTE(dperny): this doens't actually do a whole bunch for us,
			// because the only state persisted in this version of the
			// Allocator is that of allocated services, but this future-proofs
			// the test at basically no cost.
			a.Restore(initNetworks, initServices, initTasks, initNodes)
		})

		Describe("allocating networks", func() {
			var (
				net *api.Network
				err error
			)
			BeforeEach(func() {
				net = &api.Network{
					ID: "net1",
				}
			})
			JustBeforeEach(func() {
				err = a.AllocateNetwork(net)
			})
			Context("when the network is overlay", func() {
				BeforeEach(func() {
					mockDriver.EXPECT().IsNetworkNodeLocal(net).Return(false, nil)
					mockIpam.EXPECT().AllocateNetwork(net).Return(nil)
					mockDriver.EXPECT().Allocate(net).Return(nil)
				})
				It("should return no error", func() {
					Expect(err).ToNot(HaveOccurred())
				})
				Context("when the network is an ingress network", func() {
					BeforeEach(func() {
						net.Spec.Ingress = true
					})
					It("should set the ingress ID", func() {
						Expect(a.ingressID).To(Equal("net1"))
					})
				})
			})
			Context("when the network is node-local", func() {
				BeforeEach(func() {
					mockDriver.EXPECT().IsNetworkNodeLocal(net).Return(true, nil)
					mockDriver.EXPECT().Allocate(net).Return(nil)
				})
				It("should not call the IPAM allocator", func() {
					// covered by mock
				})
				It("should return no error", func() {
					Expect(err).ToNot(HaveOccurred())
				})
			})
			Context("when the network driver is invalid", func() {
				rerr := errors.ErrInvalidSpec("invalid driver")
				BeforeEach(func() {
					mockDriver.EXPECT().IsNetworkNodeLocal(net).Return(false, rerr)
				})
				It("should return the error returned by IsNetworkNodeLocal", func() {
					Expect(err).To(HaveOccurred())
					Expect(err).To(Equal(rerr))
				})
				It("should not modify the object", func() {
					Expect(net).To(Equal(&api.Network{ID: "net1"}))
				})
			})
			Context("when the IPAM allocator returns an error", func() {
				rerr := errors.ErrInternal("foo")
				BeforeEach(func() {
					mockDriver.EXPECT().IsNetworkNodeLocal(net).Return(false, nil)
					mockIpam.EXPECT().AllocateNetwork(net).Return(rerr)
				})
				It("should return the error returned by ipam.AllocateNetwork", func() {
					Expect(err).To(HaveOccurred())
					Expect(err).To(Equal(rerr))
				})
				It("should not modify the object", func() {
					Expect(net).To(Equal(&api.Network{ID: "net1"}))
				})
			})
			Context("when the driver allocator returns an error", func() {
				rerr := errors.ErrInternal("foo")
				BeforeEach(func() {
					mockDriver.EXPECT().IsNetworkNodeLocal(net).Return(false, nil)
					mockIpam.EXPECT().AllocateNetwork(net).Return(nil)
					mockDriver.EXPECT().Allocate(net).Return(rerr)
					mockIpam.EXPECT().DeallocateNetwork(net)
				})
				It("should return the error returned by driver.Allocate", func() {
					Expect(err).To(HaveOccurred())
					Expect(err).To(Equal(rerr))
				})
				It("should roll back the IPAM allocations", func() {
					// this is another case here just for documentation, it is
					// covered by gomock
				})
				It("should not modify the object", func() {
					Expect(net).To(Equal(&api.Network{ID: "net1"}))
				})
			})
		})

		Describe("deallocating networks", func() {
			var (
				network *api.Network
				err     error
			)

			BeforeEach(func() {
				network = &api.Network{
					ID: "ingressNet",
					Spec: api.NetworkSpec{
						Ingress: true,
					},
				}

				// initialize an ingress network
				initNetworks = append(initNetworks, network)
			})

			Context("when the ingress network is being deallocated", func() {
				BeforeEach(func() {
					mockDriver.EXPECT().Deallocate(network).Return(nil)
					mockIpam.EXPECT().DeallocateNetwork(network)
				})
				JustBeforeEach(func() {
					err = a.DeallocateNetwork(network)
				})
				It("should not return an error", func() {
					Expect(err).ToNot(HaveOccurred())
				})
				It("should unset the ingress ID", func() {
					Expect(a.ingressID).To(Equal(""))
				})
			})
		})

		Describe("allocating services", func() {
			var (
				service *api.Service
				err     error
			)
			BeforeEach(func() {
				// add an ingress network
				ingress := &api.Network{
					ID: "ingress",
					Spec: api.NetworkSpec{
						Ingress: true,
					},
				}
				local := &api.Network{
					ID: "localnet",
					DriverState: &api.Driver{
						Name: "local",
					},
				}
				initNetworks = append(initNetworks, ingress, local)

				initService := &api.Service{
					ID: "service1",
					SpecVersion: &api.Version{
						Index: 1,
					},
					Spec: api.ServiceSpec{
						Endpoint: &api.EndpointSpec{
							Mode: api.ResolutionModeVirtualIP,
							Ports: []*api.PortConfig{
								{
									Name:          "foo",
									TargetPort:    80,
									PublishedPort: 8080,
									Protocol:      api.ProtocolTCP,
									PublishMode:   api.PublishModeIngress,
								},
							},
						},
						Task: api.TaskSpec{
							Networks: []*api.NetworkAttachmentConfig{
								{
									Target: "nw1",
								},
							},
						},
					},
					Endpoint: &api.Endpoint{
						Spec: &api.EndpointSpec{
							Mode: api.ResolutionModeVirtualIP,
							Ports: []*api.PortConfig{
								{
									Name:          "foo",
									TargetPort:    80,
									PublishedPort: 8080,
									Protocol:      api.ProtocolTCP,
									PublishMode:   api.PublishModeIngress,
								},
							},
						},
						Ports: []*api.PortConfig{
							{
								Name:          "foo",
								TargetPort:    80,
								PublishedPort: 8080,
								Protocol:      api.ProtocolTCP,
								PublishMode:   api.PublishModeIngress,
							},
						},
						VirtualIPs: []*api.Endpoint_VirtualIP{
							{
								Addr:      "192.168.3.3/24",
								NetworkID: "nw1",
							},
							{
								Addr:      "192.168.4.3/24",
								NetworkID: "ingress",
							},
						},
					},
				}
				initServices = append(initServices, initService)

				service = initService.Copy()
			})
			JustBeforeEach(func() {
				err = a.AllocateService(service)
			})
			Context("when the exact same service is passed", func() {
				It("should return ErrAlreadyAllocated", func() {
					Expect(err).To(And(
						HaveOccurred(),
						WithTransform(errors.IsErrAlreadyAllocated, BeTrue()),
					))
				})
			})
			Context("when the service is already fully allocated", func() {
				BeforeEach(func() {
					service.SpecVersion.Index = 5
				})
				It("should return ErrAlreadyAllocated", func() {
					Expect(err).To(And(
						HaveOccurred(),
						WithTransform(errors.IsErrAlreadyAllocated, BeTrue()),
					))
				})
				It("should update the locally cached service", func() {
					Expect(a.services).To(HaveKey(service.ID))
					Expect(a.services[service.ID].SpecVersion.Index).To(Equal(uint64(5)))
				})
			})
			Context("when the service's tasks have node-local network attachments", func() {
				BeforeEach(func() {
					service.Spec.Task.Networks = append(
						service.Spec.Task.Networks,
						&api.NetworkAttachmentConfig{
							Target: "localnet",
						},
					)
				})
				It("should not allocate a VIP for the node-local network", func() {
					Expect(a.nodeLocalNetworks).To(HaveKey("localnet"))
					// covered by gomock
				})
			})
			Context("when the port allocator returns an error", func() {
				var (
					serviceCopy *api.Service
				)
				BeforeEach(func() {
					service = &api.Service{
						ID: "portErrService",
						Spec: api.ServiceSpec{
							Endpoint: &api.EndpointSpec{
								Ports: []*api.PortConfig{
									{
										TargetPort:    80,
										PublishedPort: 8080,
										Protocol:      api.ProtocolTCP,
									},
								},
							},
						},
					}
					serviceCopy = service.Copy()
					mockPort.EXPECT().Allocate(
						&api.Endpoint{}, service.Spec.Endpoint,
					).Return(nil, errors.ErrResourceInUse("port", "8080/TCP"))
				})
				It("should not alter the object", func() {
					Expect(service).To(Equal(serviceCopy))
				})
				It("should not cache the service", func() {
					Expect(a.services).NotTo(HaveKey("portErrService"))
				})
				It("should return an error", func() {
					Expect(err).To(HaveOccurred())
					Expect(err).To(WithTransform(errors.IsErrResourceInUse, BeTrue()))
					Expect(err.Error()).To(Equal("port 8080/TCP is in use"))
				})
			})
			Context("when the IPAM allocator returns an error", func() {
				var (
					prop        *fakeProposal
					serviceCopy *api.Service
				)
				BeforeEach(func() {
					service = &api.Service{
						ID: "portExposedService",
						Spec: api.ServiceSpec{
							Task: api.TaskSpec{
								Networks: []*api.NetworkAttachmentConfig{
									{
										Target: "nw1",
									},
								},
							},
							Endpoint: &api.EndpointSpec{
								Ports: []*api.PortConfig{
									{
										TargetPort:    777,
										PublishedPort: 999,
										PublishMode:   api.PublishModeIngress,
										Protocol:      api.ProtocolTCP,
									},
								},
							},
						},
					}
					serviceCopy = service.Copy()
					prop = &fakeProposal{
						ports: []*api.PortConfig{
							{
								TargetPort:    777,
								PublishedPort: 999,
								PublishMode:   api.PublishModeIngress,
								Protocol:      api.ProtocolTCP,
							},
						},
					}
					mockPort.EXPECT().Allocate(
						&api.Endpoint{}, service.Spec.Endpoint,
					).Return(prop, nil)
					mockIpam.EXPECT().AllocateVIPs(
						&api.Endpoint{},
						map[string]struct{}{"ingress": {}, "nw1": {}},
					).Return(errors.ErrResourceExhausted("ip address", "pool is full"))
				})
				It("should not commit the port allocator proposal", func() {
					Expect(prop.isCommitted).To(BeFalse())
				})
				It("should not modify the service object", func() {
					Expect(service).To(Equal(serviceCopy))
				})
				It("should return an error", func() {
					Expect(err).To(HaveOccurred())
					Expect(err).To(WithTransform(
						errors.IsErrResourceExhausted, BeTrue(),
					))
				})
			})

			Context("when the IPAM allocator return ErrAlreadyAllocated", func() {
				var (
					prop *fakeProposal
				)
				BeforeEach(func() {
					service = &api.Service{
						ID: "portExposedService",
						Spec: api.ServiceSpec{
							Task: api.TaskSpec{
								Networks: []*api.NetworkAttachmentConfig{},
							},
							Endpoint: &api.EndpointSpec{
								Ports: []*api.PortConfig{
									{
										TargetPort:    777,
										PublishedPort: 999,
										PublishMode:   api.PublishModeIngress,
										Protocol:      api.ProtocolTCP,
									},
								},
							},
						},
						Endpoint: &api.Endpoint{
							Spec: &api.EndpointSpec{
								Ports: []*api.PortConfig{
									{
										TargetPort:    777,
										PublishedPort: 777,
										PublishMode:   api.PublishModeIngress,
										Protocol:      api.ProtocolTCP,
									},
								},
							},
							Ports: []*api.PortConfig{
								{
									TargetPort:    777,
									PublishedPort: 777,
									PublishMode:   api.PublishModeIngress,
									Protocol:      api.ProtocolTCP,
								},
							},
							VirtualIPs: []*api.Endpoint_VirtualIP{
								{
									NetworkID: "ingress",
									Addr:      "192.168.3.123/24",
								},
							},
						},
					}
					prop = &fakeProposal{
						ports: []*api.PortConfig{
							{
								TargetPort:    777,
								PublishedPort: 999,
								PublishMode:   api.PublishModeIngress,
								Protocol:      api.ProtocolTCP,
							},
						},
					}
					mockPort.EXPECT().Allocate(
						service.Endpoint, service.Spec.Endpoint,
					).Return(prop, nil)
					mockIpam.EXPECT().AllocateVIPs(
						service.Endpoint,
						map[string]struct{}{"ingress": {}},
					).Return(errors.ErrAlreadyAllocated())
				})
				It("should not return an error", func() {
					Expect(err).ToNot(HaveOccurred())
				})
				It("should commit the port allocations", func() {
					Expect(prop.isCommitted).To(BeTrue())
				})
				It("should cache the service", func() {
					Expect(a.services).To(HaveKey(service.ID))
					Expect(a.services[service.ID]).To(Equal(service))
				})
			})
			Context("when a new service with ports and attachments is allocated", func() {
				var (
					prop *fakeProposal
				)
				BeforeEach(func() {
					service = &api.Service{
						ID: "portExposedService",
						Spec: api.ServiceSpec{
							Task: api.TaskSpec{
								Networks: []*api.NetworkAttachmentConfig{
									{
										Target: "nw1",
									},
								},
							},
							Endpoint: &api.EndpointSpec{
								Ports: []*api.PortConfig{
									{
										TargetPort:    777,
										PublishedPort: 999,
										PublishMode:   api.PublishModeIngress,
										Protocol:      api.ProtocolTCP,
									},
								},
							},
						},
					}

					prop = &fakeProposal{
						ports: []*api.PortConfig{
							{
								TargetPort:    777,
								PublishedPort: 999,
								PublishMode:   api.PublishModeIngress,
								Protocol:      api.ProtocolTCP,
							},
						},
					}
					mockPort.EXPECT().Allocate(
						&api.Endpoint{}, service.Spec.Endpoint,
					).Return(prop, nil)
					mockIpam.EXPECT().AllocateVIPs(
						&api.Endpoint{}, map[string]struct{}{"ingress": {}, "nw1": {}},
					).Do(func(endpoint *api.Endpoint, _ map[string]struct{}) {
						endpoint.VirtualIPs = []*api.Endpoint_VirtualIP{
							{
								NetworkID: "ingress",
								Addr:      "192.168.4.123/24",
							},
							{
								NetworkID: "nw1",
								Addr:      "192.168.3.123/24",
							},
						}
					}).Return(
						nil,
					)
				})
				It("should allocate a VIP on the ingress network", func() {
					// covered by gomock
				})
				It("should return no error", func() {
					Expect(err).ToNot(HaveOccurred())
				})
				It("should fill in the object's endpoint", func() {
					Expect(service.Endpoint).ToNot(BeNil())
					Expect(service.Endpoint.VirtualIPs).To(ConsistOf(
						&api.Endpoint_VirtualIP{
							NetworkID: "ingress",
							Addr:      "192.168.4.123/24",
						},
						&api.Endpoint_VirtualIP{
							NetworkID: "nw1",
							Addr:      "192.168.3.123/24",
						},
					))
					Expect(service.Endpoint.Ports).To(ConsistOf(
						&api.PortConfig{
							TargetPort:    777,
							PublishedPort: 999,
							PublishMode:   api.PublishModeIngress,
							Protocol:      api.ProtocolTCP,
						},
					))
					Expect(service.Endpoint.Spec).To(Equal(service.Spec.Endpoint))
				})
				It("should cache the service", func() {
					Expect(a.services).To(HaveKey(service.ID))
					Expect(a.services[service.ID]).To(Equal(service))
				})
				It("should commit the port allocation", func() {
					Expect(prop.isCommitted).To(BeTrue())
				})
			})
			Context("when no ingress network is currently allocated", func() {
				BeforeEach(func() {
					// clear out initNetworks and initServices, so that no
					// ingress network and no service will be restored, and we
					// have a clean allocator
					initNetworks = []*api.Network{}

					// create a minimal service that exposes some ports, so the
					// network will try to attach to ingress
					service = &api.Service{
						Spec: api.ServiceSpec{
							Endpoint: &api.EndpointSpec{
								Ports: []*api.PortConfig{
									{
										TargetPort: 80,
										Protocol:   api.ProtocolTCP,
									},
								},
							},
						},
					}

					mockPort.EXPECT().Allocate(&api.Endpoint{}, service.Spec.Endpoint).Return(
						&fakeProposal{
							ports: []*api.PortConfig{
								{
									TargetPort:    80,
									Protocol:      api.ProtocolTCP,
									PublishMode:   api.PublishModeIngress,
									PublishedPort: 30303,
								},
							},
						}, nil,
					)
				})

				It("should fail with ErrDependencyNotAllocated", func() {
					Expect(err).To(HaveOccurred())
					Expect(err).To(WithTransform(errors.IsErrDependencyNotAllocated, BeTrue()))
					Expect(err.Error()).To(Equal("network ingress depended on by object is not allocated"))
				})
			})
		})

		Describe("allocating tasks", func() {
			var (
				service *api.Service
				task    *api.Task
				err     error

				ingress, localnet, nw1, nw2 *api.Network
			)
			BeforeEach(func() {
				// we'll need an ingress network for these tests, so add one to
				// the initNetworks
				ingress = &api.Network{
					ID: "allocTaskIngressNw",
					Spec: api.NetworkSpec{
						Ingress: true,
					},
				}

				// add a node-local network, which shouldn't be allocated on
				// the task
				localnet = &api.Network{
					ID: "allocTaskLocalNw",
					Spec: api.NetworkSpec{
						DriverConfig: &api.Driver{
							Name: "local",
						},
					},
					DriverState: &api.Driver{
						Name: "local",
					},
				}

				nw1 = &api.Network{
					ID: "allocTaskNw1",
				}
				nw2 = &api.Network{
					ID: "allocTaskNw2",
				}

				initNetworks = append(initNetworks, ingress, localnet, nw1, nw1)

				// create a service which will be for our tasks
				service = &api.Service{
					ID: "allocTaskService",
					Endpoint: &api.Endpoint{
						Spec: &api.EndpointSpec{
							Mode: api.ResolutionModeVirtualIP,
							Ports: []*api.PortConfig{
								{
									TargetPort:    80,
									PublishedPort: 80,
									Protocol:      api.ProtocolTCP,
									PublishMode:   api.PublishModeIngress,
								},
							},
						},
						Ports: []*api.PortConfig{
							{
								TargetPort:    80,
								PublishedPort: 80,
								Protocol:      api.ProtocolTCP,
								PublishMode:   api.PublishModeIngress,
							},
						},
						VirtualIPs: []*api.Endpoint_VirtualIP{
							{
								NetworkID: "allocTaskNw1",
							},
							{
								NetworkID: "allocTaskNw2",
							},
							{
								NetworkID: "allocTaskIngressNw",
							},
						},
					},
					Spec: api.ServiceSpec{
						Task: api.TaskSpec{
							Networks: []*api.NetworkAttachmentConfig{
								{
									Target: "allocTaskLocalNw",
									// include some opts so that we can be sure
									// fields are correctly carried
									DriverAttachmentOpts: map[string]string{
										"foo": "bar",
									},
								},
								{
									Target: "allocTaskNw1",
								},
								{
									Target: "allocTaskNw2",
								},
							},
						},
						Endpoint: &api.EndpointSpec{
							Mode: api.ResolutionModeVirtualIP,
							Ports: []*api.PortConfig{
								{
									TargetPort:    80,
									PublishedPort: 80,
									Protocol:      api.ProtocolTCP,
									PublishMode:   api.PublishModeIngress,
								},
							},
						},
					},
				}
				initServices = append(initServices, service)
			})

			JustBeforeEach(func() {
				// allocate the task object
				err = a.AllocateTask(task)
			})

			Context("when successfully allocating a task", func() {
				BeforeEach(func() {
					task = &api.Task{
						ID: "allocTaskTask",
						Status: api.TaskStatus{
							State: api.TaskStateNew,
						},
						DesiredState: api.TaskStateRunning,
						ServiceID:    service.ID,
						Spec:         service.Spec.Task,
					}
					mockIpam.EXPECT().AllocateAttachment(
						task.Spec.Networks[1],
					).Return(
						&api.NetworkAttachment{
							Network: nw1,
						}, nil,
					)
					mockIpam.EXPECT().AllocateAttachment(
						task.Spec.Networks[2],
					).Return(
						&api.NetworkAttachment{
							Network: nw2,
						}, nil,
					)
					mockIpam.EXPECT().AllocateAttachment(
						&api.NetworkAttachmentConfig{Target: ingress.ID},
					).Return(
						&api.NetworkAttachment{
							Network: ingress,
						}, nil,
					)
				})

				It("should not return an error", func() {
					Expect(err).ToNot(HaveOccurred())
				})
				It("should fill in the task's networks", func() {
					// including ingress and the local network
					Expect(task.Networks).To(ConsistOf(
						&api.NetworkAttachment{
							Network: localnet,
							DriverAttachmentOpts: map[string]string{
								"foo": "bar",
							},
						},
						&api.NetworkAttachment{
							Network: nw1,
						},
						&api.NetworkAttachment{
							Network: nw2,
						},
						&api.NetworkAttachment{
							Network: ingress,
						},
					))
				})
				It("should populate the task's endpoint with the service's endpoint", func() {
					Expect(task.Endpoint).To(Equal(service.Endpoint))
				})
			})
		})

		Describe("allocating nodes", func() {
			var (
				node     *api.Node
				networks map[string]struct{}
				err      error

				ingress, nw1, nw2 *api.Network
			)

			BeforeEach(func() {
				ingress = &api.Network{
					ID: "allocNodesIngress",
					Spec: api.NetworkSpec{
						Ingress: true,
					},
				}

				nw1 = &api.Network{
					ID: "allocNodesNw1",
				}
				nw2 = &api.Network{
					ID: "allocNodesNw2",
				}

				initNetworks = append(initNetworks, ingress, nw1, nw2)

				networks = map[string]struct{}{
					"allocNodesIngress": {},
					"allocNodesNw1":     {},
					"allocNodesNw2":     {},
				}

				node = &api.Node{}
			})

			JustBeforeEach(func() {
				err = a.AllocateNode(node, networks)
			})
			Context("when a new node is successfully allocated", func() {
				BeforeEach(func() {
					mockIpam.EXPECT().AllocateAttachment(
						&api.NetworkAttachmentConfig{Target: "allocNodesIngress"},
					).Return(
						&api.NetworkAttachment{
							Network: ingress,
						}, nil,
					)

					mockIpam.EXPECT().AllocateAttachment(
						&api.NetworkAttachmentConfig{Target: "allocNodesNw1"},
					).Return(
						&api.NetworkAttachment{
							Network: nw1,
						}, nil,
					)

					mockIpam.EXPECT().AllocateAttachment(
						&api.NetworkAttachmentConfig{Target: "allocNodesNw2"},
					).Return(
						&api.NetworkAttachment{
							Network: nw2,
						}, nil,
					)
				})
				It("should not return an error", func() {
					Expect(err).ToNot(HaveOccurred())
				})
				It("should include all of the networks", func() {
					Expect(node.Attachments).To(ConsistOf(
						&api.NetworkAttachment{
							Network: ingress,
						},
						&api.NetworkAttachment{
							Network: nw1,
						},
						&api.NetworkAttachment{
							Network: nw2,
						},
					))
				})
			})

			Context("when a node is already fully allocated", func() {
				BeforeEach(func() {
					node.Attachments = []*api.NetworkAttachment{
						{
							Network: nw1,
						},
						{
							Network: nw2,
						},
						{
							Network: ingress,
						},
					}
				})
				It("should return ErrAlreadyAllocated", func() {
					Expect(err).To(HaveOccurred())
					Expect(err).To(WithTransform(errors.IsErrAlreadyAllocated, BeTrue()))
				})
			})

			Context("when a network is added to an existing node", func() {
				BeforeEach(func() {
					node.Attachments = []*api.NetworkAttachment{
						{
							Network:              nw1,
							DriverAttachmentOpts: map[string]string{"foo": "bar"},
						},
						{
							Network:              ingress,
							DriverAttachmentOpts: map[string]string{"baz": "bat"},
						},
					}
					mockIpam.EXPECT().AllocateAttachment(
						&api.NetworkAttachmentConfig{Target: "allocNodesNw2"},
					).Return(
						&api.NetworkAttachment{
							Network: nw2,
						}, nil,
					)
				})
				It("should not return an error", func() {
					Expect(err).ToNot(HaveOccurred())
				})
				It("should include all of the networks", func() {
					Expect(node.Attachments).To(ConsistOf(
						&api.NetworkAttachment{
							Network:              ingress,
							DriverAttachmentOpts: map[string]string{"baz": "bat"},
						},
						&api.NetworkAttachment{
							Network:              nw1,
							DriverAttachmentOpts: map[string]string{"foo": "bar"},
						},
						&api.NetworkAttachment{
							Network: nw2,
						},
					))
				})
			})

			Context("when a network is removed from an existing node", func() {
				BeforeEach(func() {
					node.Attachments = []*api.NetworkAttachment{
						{
							Network:              nw1,
							DriverAttachmentOpts: map[string]string{"foo": "bar"},
						},
						{
							Network:              ingress,
							DriverAttachmentOpts: map[string]string{"baz": "bat"},
						},
						{
							Network: nw2,
						},
					}
					delete(networks, nw2.ID)

					mockIpam.EXPECT().DeallocateAttachment(
						&api.NetworkAttachment{Network: nw2},
					).Return(nil)
				})
				It("should not return an error", func() {
					Expect(err).ToNot(HaveOccurred())
				})
				It("should include all of the networks", func() {
					Expect(node.Attachments).To(ConsistOf(
						&api.NetworkAttachment{
							Network:              ingress,
							DriverAttachmentOpts: map[string]string{"baz": "bat"},
						},
						&api.NetworkAttachment{
							Network:              nw1,
							DriverAttachmentOpts: map[string]string{"foo": "bar"},
						},
					))
				})
			})
		})
	})

	Describe("isServiceFullyAllocated", func() {
		var (
			service *api.Service
			result  bool
		)
		BeforeEach(func() {
			// create a service pre-populated with all of the pointer values so we
			// can just do assignments in the tests
			service = &api.Service{
				Spec: api.ServiceSpec{
					Endpoint: &api.EndpointSpec{},
				},
				Endpoint: &api.Endpoint{
					Spec: &api.EndpointSpec{},
				},
			}
		})
		JustBeforeEach(func() {
			result = a.isServiceFullyAllocated(service)
		})
		Context("when the spec and endpoint are both nil", func() {
			BeforeEach(func() {
				service.Endpoint = nil
				service.Spec.Endpoint = nil
			})
			It("should return true", func() {
				Expect(result).To(BeTrue())
			})
		})
		Context("when the service's resolution mode does not match the spec's", func() {
			BeforeEach(func() {
				service.Endpoint.Spec.Mode = api.ResolutionModeDNSRoundRobin
				service.Spec.Endpoint.Mode = api.ResolutionModeVirtualIP
			})
			It("should return false", func() {
				Expect(result).To(BeFalse())
			})
		})
		Context("when the endpoint VIPs and network attachments have different lengths", func() {
			BeforeEach(func() {
				service.Endpoint.VirtualIPs = []*api.Endpoint_VirtualIP{
					{
						NetworkID: "nw1",
						Addr:      "192.168.1.1/24",
					},
				}
				service.Spec.Task.Networks = []*api.NetworkAttachmentConfig{
					{
						Target: "nw1",
					},
					{
						Target: "nw2",
					},
				}
			})
			It("should return false", func() {
				Expect(result).To(BeFalse())
			})
		})
		Context("when the endpoint has VIPs for the wrong networks", func() {
			BeforeEach(func() {
				service.Endpoint.VirtualIPs = []*api.Endpoint_VirtualIP{
					{
						NetworkID: "nw1",
						Addr:      "192.168.1.1/24",
					},
					{
						NetworkID: "nw3",
						Addr:      "192.168.2.1/24",
					},
				}
				service.Spec.Task.Networks = []*api.NetworkAttachmentConfig{
					{
						Target: "nw1",
					},
					{
						Target: "nw2",
					},
				}
			})
			It("should return false", func() {
				Expect(result).To(BeFalse())
			})
		})

		Context("when the ports do not match", func() {
			BeforeEach(func() {
				// we don't need to test the functionality of AlreadyAllocated,
				// just create a case where we know it will return false.
				service.Spec.Endpoint.Ports = []*api.PortConfig{
					{
						Name: "foo",
					},
				}
			})
			It("should return false", func() {
				Expect(result).To(BeFalse())
			})
		})

		Context("when the service is totally empty", func() {
			BeforeEach(func() {
				service = &api.Service{ID: "foo"}
			})
			It("should return true", func() {
				Expect(result).To(BeTrue())
			})
		})

		Context("when the task spec has local networks", func() {
			BeforeEach(func() {
				a.nodeLocalNetworks["localnet"] = &api.Network{}
				service.Spec.Task.Networks = []*api.NetworkAttachmentConfig{
					{
						Target: "localnet",
					},
				}
			})
			It("should return true", func() {
				Expect(result).To(BeTrue())
			})
		})

		Context("when a network has more than 1 vip allocated", func() {
			BeforeEach(func() {
				service.Endpoint.VirtualIPs = []*api.Endpoint_VirtualIP{
					{
						NetworkID: "nw1",
						Addr:      "192.168.1.1/24",
					},
					{
						NetworkID: "nw1",
						Addr:      "192.168.2.1/24",
					},
				}
				service.Spec.Task.Networks = []*api.NetworkAttachmentConfig{
					{
						Target: "nw1",
					},
					{
						Target: "nw2",
					},
				}
			})
			It("should return false", func() {
				Expect(result).To(BeFalse())
			})
		})
	})
})
